-- Prove2me | Theorems.Thm_DetCCHard_Supplement_theorem_9_6
-- name    : DetCCHard.Supplement.theorem_9_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:37:04.325038+00:00
-- url     : https://prove2.me/theorems/4d8bc7bc-c332-498e-8399-f1fa0f20ca6b
-- title:
--   Theorem 9.6 — randomized reduction: square power-of-two tables with YES cost $\le B_k$ and NO cost $= B_k + k$ with probability $\ge 49/50$
-- statement:
--   There is a randomized algorithm that, given a source graph on $n$ vertices above the fixed cutoff of Lemma F.2 and an integer $k \ge 1$, outputs a total Boolean matrix $M$ and an integer $B$. The table is square with power-of-two side length
--   $$
--   m = \mathrm{pow}_2\bigl(16(r_k + 1)\lceil \log(r_k + 2) \rceil 2^{H_k}\bigr),
--   $$
--   independent of the tape, and $B = B_k$, where $L = \lceil \log n \rceil$, $s = \mathrm{pow}_2(2^{16}(L+1))$, $h = L + 36\log s$, $d_0 = \log \mathrm{pow}_2(64(L+1)) + 1$, $B_k = d_0 + kh$, $H_k = B_k + k$ and $r_k = 2^{B_k - 1}$. On every tape the algorithm uses $n^{O(k+1)}$ time and random bits, with an absolute implied constant independent of $k$. For a YES source, $D(M) \le B$ on every tape. For a NO source,
--   $$
--   \Pr[D(M) = B + k] \ge 49/50 .
--   $$
--
--   Combined with an estimator, this gives the randomized branch of the tradeoff in Theorem 9.7.
--
--   **Formalization Note** The algorithm is one machine in the published Cook model reading the input $(k, G)$ and a random tape whose length depends on the input only; on every tape it halts within $n^{c(k+1)}$ steps with the encoding of $M$ and $B_k$, and the tape length is at most $n^{c(k+1)}$. The constant $c$ is chosen first. A source graph has the shape of Theorem 5.2 and is YES or NO.
--
--   Differences from the source:
--   - generalization: the fixed constants Δ, γ of Theorem 5.2 → every Δ ≥ 1 and every rational γ > 0, with the cutoffs chosen after them; reason: the pair of Theorem 5.2 is a special case
--   - reading: B = B_k with the parameters of Lemma F.2 and h = L + O(log L) → B_k = d₀ + k h with h = L + 36 log s, s = pow2(2^16(L + 1)); reason: the values of Lemma F.2 used by the algorithm
--   - encoding: a randomized algorithm using n^{O(k+1)} time and random bits on every tape, absolute constant → ∃ c before everything; one machine on input encodeRandRedInput G k plus a tape of length ℓ(input) ≤ n^{c(k+1)}, halting within n^{c(k+1)} steps on every tape; reason: the random-tape model of §4.1 and §9.3
--   - encoding: outputs M and B → the output word encodeTableNat M B_k with M an m × m table; reason: an explicit injective encoding
--   - encoding: above the fixed cutoff in Lemma F.2 → ∃ n₀ (after Δ, γ) with n₀ < n; reason: same statement
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 9.6, p.41 (parameters: Lemma F.2, p.69, §9.3, p.40)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_SrcGraph
import Definitions.Def_DetCCHard_pow2
import Definitions.Def_DetCCHard_CodeSym
import Definitions.Def_DetCCHard_Supplement_Estimator

namespace DetCCHard.Supplement

open DetCCHard

/-- **Theorem 9.6 (Randomized reduction)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256 ad552d13…a4a03, Theorem 9.6, p.41, with the parameters of
Lemma F.2, p.69, and §9.3, p.40). There is a randomized algorithm that, given a source graph on `n`
vertices above the fixed cutoff in Lemma F.2 and an integer `k ≥ 1`, outputs a total Boolean matrix
`M` and an integer `B`. The table is square with power-of-two side length. On every tape the
algorithm uses `n^{O(k+1)}` time and random bits, with an absolute implied constant independent of
`k`. For a YES source, `D(M) ≤ B` on every tape. For a NO source, `Pr[D(M) = B + k] ≥ 49/50`. Here
`B = B_k` and the tape-independent entry count is `m = pow2(16(r_k + 1)⌈log(r_k + 2)⌉ 2^{H_k})`,
`T = m²`, where `L = ⌈log n⌉`, `B_k = d₀ + kh`, `H_k = B_k + k`, `r_k = 2^{B_k − 1}`,
`d₀ = log pow2(64(L + 1)) + 1` and `h = L + 36 log s` with `s = pow2(2^{16}(L + 1))`.

**Formalization Note** The algorithm is one published one-tape machine reading
`randInput (encodeRandRedInput G k) tape`, with a tape length `ℓ` that is a function of the input
only; on every tape it halts within `n^{c(k+1)}` steps writing `encodeTableNat (out tape) B_k`, an
`m × m` table, and `ℓ ≤ n^{c(k+1)}`. The absolute constant `c` is chosen first; the machine and the
cutoff `n₀` after the graph-promise constants `Δ ≥ 1`, `γ > 0` (the paper fixes the pair of
Theorem 5.2). A source graph is any graph with the shape of Theorem 5.2 that is YES or NO, with more
than `n₀` vertices. `Pr` is the fraction of tapes; `D` is `Dcost`. -/
theorem theorem_9_6 :
    ∃ c : ℕ, ∀ Δ : ℕ, 1 ≤ Δ → ∀ γ : ℚ, 0 < γ → ∃ n₀ : ℕ,
      ∃ (Γ : Type) (_ : Fintype Γ) (ι₁ : Option (CodeSym ⊕ Bool) ↪ Γ) (ι₂ : CodeSym ↪ Γ)
        (M : CookPvsNP.TM Γ) (ℓ : List CodeSym → ℕ),
        ∀ G : SrcGraph, IsShape Δ G → (IsYes G ∨ IsNo γ G) → n₀ < G.n → ∀ k : ℕ, 1 ≤ k →
          let L := Nat.clog 2 G.n
          let s := pow2 (2 ^ 16 * (L + 1))
          let h := L + 36 * Nat.log 2 s
          let d₀ := Nat.log 2 (pow2 (64 * (L + 1))) + 1
          let B := d₀ + k * h
          let Hk := B + k
          let rk := 2 ^ (B - 1)
          let m := pow2 (16 * (rk + 1) * Nat.clog 2 (rk + 2) * 2 ^ Hk)
          let x := encodeRandRedInput G k
          ℓ x ≤ G.n ^ (c * (k + 1)) ∧
          ∃ out : (Fin (ℓ x) → Bool) → Fin m → Fin m → Bool,
            (∀ tape : Fin (ℓ x) → Bool,
              RunsWithin M ι₁ ι₂ (randInput x (List.ofFn tape)) (G.n ^ (c * (k + 1)))
                (encodeTableNat (out tape) B)) ∧
            (IsYes G → ∀ tape : Fin (ℓ x) → Bool, Dcost (out tape) ≤ B) ∧
            (IsNo γ G → (49 / 50 : ℚ) ≤
              tapeFrac (ℓ x) (fun tape => Dcost (out tape) = B + k)) := by sorry

end DetCCHard.Supplement
