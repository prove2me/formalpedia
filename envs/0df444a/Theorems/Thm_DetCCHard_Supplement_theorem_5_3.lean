-- Prove2me | Theorems.Thm_DetCCHard_Supplement_theorem_5_3
-- name    : DetCCHard.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:57:31.623428+00:00
-- url     : https://prove2.me/theorems/3f8f079a-e2ac-4c31-a18e-6f5219d4d184
-- title:
--   Theorem 5.3 — one amplification round $R \mapsto R^+$: YES cost $\le D(R) + h$, NO cost $= d + h + 1$ with restored deletion bounds, rank $\le 2^h \operatorname{rank}(R)$
-- statement:
--   Let $G = (V, E)$ be a YES or NO graph produced by Theorem 5.2, and put $n = |V|$. The construction $R \mapsto R^+$ of Definition 6.2 (full products) or Definition 8.3 (explicit lists) acts on base matrices $R$ with positive normalized rational input weights, with a public row-weight threshold $\rho$ and a public integer $h$:
--
--   1. **Full-product case.** $n$ exceeds an effectively computable constant, $L = \lceil \log n \rceil$, $\rho = 2^{-L}$, $s = \mathrm{pow}_2(2^{16}(L+1))$ and $h = L + 36 \log s = L + O_{\Delta,\gamma}(\log L)$.
--   2. **Explicit case.** $s$ is a power of two with $s \ge s_0$ and $s^4 \ge n$, $N = s^4$, $\rho = 1/N$ and $h = 10 \log N$.
--
--   In both cases:
--
--   (i) on either source promise $D(R^+) \le D(R) + h + 1$, and, if $G$ is YES, $D(R^+) \le D(R) + h$;
--
--   (ii) if $G$ is NO and $D(R) = d \ge 3$ and $\mathcal P(R; \rho, d)$, then
--   $$
--   D(R^+) = d + h + 1, \qquad \mathcal P(R^+; \rho, d + h + 1);
--   $$
--
--   (iii) on either source promise $\operatorname{rank}(R^+) \le 2^h \operatorname{rank}(R)$.
--
--   One round adds $h$ bits to the YES upper bound and $h + 1$ bits to the NO lower bound while restoring the deletion bounds the next round needs; iterating it (Proposition 5.5) builds the additive gap.
--
--   **Formalization Note** The construction is the paper's own, with $w = s^8$, $Q = s^{24}$, $q_2 = s^2/\rho$ ($= s^2 2^L$, resp. $s^6$), and the statement also asserts that $q_2$ is a dyadic multiple of $q_0 = \mathrm{pow}_2(4s|E|)$. In the explicit case all lists are arbitrary exactly 8192-wise independent lists with the prescribed marginals (Γ-list, template list, bin tuples, the three label sequences of $U$, the outer list with the column weights of $W$), and the $\Omega$-tails are those induced by the Γ-list. $R^+$ has the outer-list weights on its rows and the weights $\nu_U(\ell)/Q$ on its columns.
--
--   Differences from the source:
--   - reading: there are a public ρ, a public h and a deterministic, implicitly represented construction R ↦ R⁺ → the paper's construction of Definitions 6.2 / 8.3 with ρ and h given explicitly; reason: an existential construction could branch on whether G is 3-colorable and lose the content; the named construction implies the existential statement
--   - reading: h = L + O_{Δ,γ}(log L) (full-product case) → h = L + 36 log s with s = pow2(2^16(L + 1)); reason: the value of h in Lemma F.2 and in the proof of Theorem 5.3 (h = 2 log s + log q₂ + log w + log Q), which is L + O(log L)
--   - generalization: the Code8192 lists of Lemma 7.1 in Definition 8.3 → any lists with positive normalized weights that are exactly 8192-wise independent with the prescribed marginals; reason: the Code8192 lists are such lists; the proof uses only their exact independence and marginals
--   - generalization: N = s⁴ for the power of two s of Lemma F.3 (the least dyadic s ≥ max{n^{1/4}, s₀}) → every dyadic s ≥ s₀ with s⁴ ≥ n; reason: Lemma F.3 states that every such s satisfies the bounds; the least one is a special case
--   - generalization: the fixed constants Δ, γ of Theorem 5.2 → every Δ ≥ 1 and every rational γ > 0, with the cutoffs chosen after them; reason: the pair of Theorem 5.2 is a special case
--   - reading: Ω-column weights in the explicit case: "the weights induced on the tail by Γ_g" → the tail list of the Γ-list, one Ω-tail label per Γ-label with its weight; reason: inputs with equal decoded values keep separate labels and weights (p.35)
--   - encoding: the 2s − 1 positions of γ, blocks [q], positions π_α(i) ∈ {1, …, s + 1} → positions Fin (s − 2) ⊕ Fin (s + 1), 0-based blocks and positions; reason: bijective reindexing
--   - encoding: a fixed order on I → every injection of I into ℕ; reason: the paper leaves the order unspecified; the statement holds for each
--   - encoding: n must exceed an effectively computable constant → ∃ n₀ with n₀ < n; reason: same statement; effectivity is not formalized
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 5.3, p.17 (proof on p.32; parameters: Definition 6.1, p.18, Lemmas F.2 and F.3, p.69)

import Mathlib
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_DeletionBounds
import Definitions.Def_DetCCHard_TupleList
import Definitions.Def_DetCCHard_interlaceOn
import Definitions.Def_DetCCHard_realRank
import Definitions.Def_DetCCHard_SrcGraph
import Definitions.Def_DetCCHard_pow2
import Definitions.Def_DetCCHard_Item
import Definitions.Def_DetCCHard_WMat
import Definitions.Def_DetCCHard_Supplement_RawList
import Definitions.Def_DetCCHard_Supplement_SrcData
import Definitions.Def_DetCCHard_Supplement_Ineq10

namespace DetCCHard.Supplement

open DetCCHard

/-- **Theorem 5.3 (Amplification under input deletion)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256 ad552d13…a4a03, Theorem 5.3, p.17; proof p.32, with
the parameters of Definition 6.1, p.18, Lemma F.2 and Lemma F.3, p.69). Let `G = (V, E)` be a YES
or NO graph produced by Theorem 5.2, and put `n = |V|`. In either case there are a public row-weight
threshold `ρ`, a public integer `h`, and a deterministic, implicitly represented construction
`R ↦ R⁺` on base matrices `R` with positive normalized rational input weights. In the full-product
case, `n` must exceed an effectively computable constant, `ρ = 2^{-L}` with `L = ⌈log n⌉`, and
`h = L + O_{Δ,γ}(log L)`. In the explicit case, `ρ = 1/N` and `h = 10 log N`, with `N = s⁴` for the
power of two `s` of Lemma F.3. In both cases:
(i) on either source promise, `D(R⁺) ≤ D(R) + h + 1`, and, if `G` is YES, `D(R⁺) ≤ D(R) + h`;
(ii) if `G` is NO and `D(R) = d ≥ 3` and `P(R; ρ, d)`, then `D(R⁺) = d + h + 1` and
`P(R⁺; ρ, d + h + 1)`;
(iii) on either source promise, `rank(R⁺) ≤ 2^h rank(R)`.

**Formalization Note** The construction is the paper's own (Definition 6.2 / 8.3), the
list-parametrized `SrcData` with `U = I_w(N)`, `W = Uᵀ`, `R⁺ = (I_Q(W))ᵀ`, `w = s⁸`, `Q = s^{24}`,
and `ρ`, `h` are given explicitly.
*Full-product case* (first conjunct): `L = ⌈log n⌉`, `s = pow2(2^{16}(L + 1))`, `q₂ = s² 2^L`,
`ρ = 2^{-L}`, `h = 2 log s + log q₂ + log w + log Q = L + 36 log s` (Lemma F.2), all lists full
products, for every graph with more than `n₀` vertices; it also asserts that `q₂` is a dyadic
multiple of `q₀`.
*Explicit case* (second conjunct): every dyadic `s ≥ max{n^{1/4}, s₀}`, `N = s⁴`, `ρ = 1/N`,
`q₂ = s⁶`, `h = 10 log N` (Lemma F.3), and any lists that are exactly 8192-wise independent with
the prescribed marginals (the Γ-list, the template list, the bin tuples, the three `(H3)` label
sequences of `U`, and the outer list with the column weights of `W`), with the `Ω`-tails induced by
the Γ-list; the lists of Lemma 7.1 used by Definition 8.3 are one such choice.
The source graph has the shape of Theorem 5.2 with constants `Δ ≥ 1`, `γ > 0` and is YES or NO.
`R⁺`'s rows carry the outer-list weights, its columns `(i, ℓ)` the weights `ν_U(ℓ)/Q`; the item
order is arbitrary. Logarithms are `Nat.log 2` of powers of two; rank is over `ℝ`. -/
theorem theorem_5_3 :
    (∀ Δ : ℕ, 1 ≤ Δ → ∀ γ : ℚ, 0 < γ → ∃ n₀ : ℕ, ∀ G : SrcGraph, IsShape Δ G →
      (IsYes G ∨ IsNo γ G) → n₀ < G.n →
      let L := Nat.clog 2 G.n
      let s := pow2 (2 ^ 16 * (L + 1))
      let h := L + 36 * Nat.log 2 s
      (∃ t : ℕ, q2 G s t = s ^ 2 * 2 ^ L) ∧
      ∀ (t : ℕ), q2 G s t = s ^ 2 * 2 ^ L → ∀ (ord : Item s G.n ↪ ℕ) (R : WMat),
        let D := SrcData.full R G s t ord
        let TU := D.fullU (s ^ 8)
        let TQ := D.fullQ (s ^ 8) (s ^ 24)
        Dcost (D.Rplus TU TQ) ≤ Dcost R.entry + h + 1 ∧
        (IsYes G → Dcost (D.Rplus TU TQ) ≤ Dcost R.entry + h) ∧
        (IsNo γ G → ∀ d : ℕ, Dcost R.entry = d → 3 ≤ d →
          DeletionBounds R.entry R.μX R.μY (1 / 2 ^ L) d →
          Dcost (D.Rplus TU TQ) = d + h + 1 ∧
            DeletionBounds (D.Rplus TU TQ) TQ.ν (interlaceRowWt TU.ν (s ^ 24)) (1 / 2 ^ L)
              ((d + h + 1 : ℕ) : ℤ)) ∧
        realRank (D.Rplus TU TQ) ≤ 2 ^ h * realRank R.entry) ∧
    (∀ Δ : ℕ, 1 ≤ Δ → ∀ γ : ℚ, 0 < γ → ∃ s₀ : ℕ, (∃ e : ℕ, s₀ = 2 ^ e) ∧
      (∀ (G : SrcGraph) (s : ℕ), IsShape Δ G → (∃ e : ℕ, s = 2 ^ e) → s₀ ≤ s → G.n ≤ s ^ 4 →
        ∃ t : ℕ, q2 G s t = s ^ 6) ∧
      ∀ D : SrcData, IsShape Δ D.G → (IsYes D.G ∨ IsNo γ D.G) → (∃ e : ℕ, D.s = 2 ^ e) →
        s₀ ≤ D.s → D.G.n ≤ D.s ^ 4 → D.q = D.s ^ 6 → D.TΩ = D.TΓ.tailList → D.ExplicitLists →
        ∀ (T1 : RawList D.TypeLab (Fin (D.s ^ 8))) (T2 : RawList D.R.X (Fin (D.s ^ 8)))
          (T3 : RawList D.TS.L (Fin (D.s ^ 8))), D.H3Lists T1 T2 T3 →
        ∀ TQ : RawList (Fin (D.s ^ 8) × D.NRow) (Fin (D.s ^ 24)), IsWeight TQ.ν →
          ExactlyIndepW TQ.ν TQ.z 8192 (interlaceRowWt D.NWt (D.s ^ 8)) →
        let N := D.s ^ 4
        let h := 10 * Nat.log 2 N
        let TU := D.combineH3 T1 T2 T3
        Dcost (D.Rplus TU TQ) ≤ Dcost D.R.entry + h + 1 ∧
        (IsYes D.G → Dcost (D.Rplus TU TQ) ≤ Dcost D.R.entry + h) ∧
        (IsNo γ D.G → ∀ d : ℕ, Dcost D.R.entry = d → 3 ≤ d →
          DeletionBounds D.R.entry D.R.μX D.R.μY (1 / (N : ℝ)) d →
          Dcost (D.Rplus TU TQ) = d + h + 1 ∧
            DeletionBounds (D.Rplus TU TQ) TQ.ν (interlaceRowWt TU.ν (D.s ^ 24)) (1 / (N : ℝ))
              ((d + h + 1 : ℕ) : ℤ)) ∧
        realRank (D.Rplus TU TQ) ≤ 2 ^ h * realRank D.R.entry) := by sorry

end DetCCHard.Supplement
