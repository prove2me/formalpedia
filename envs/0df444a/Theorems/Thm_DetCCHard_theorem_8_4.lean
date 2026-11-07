-- Prove2me | Theorems.Thm_DetCCHard_theorem_8_4
-- name    : DetCCHard.theorem_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:30.106641+00:00
-- url     : https://prove2.me/theorems/d8d16382-898a-4dcf-b296-6ecd094238fe
-- title:
--   Theorem 8.4 — deterministic gap tables: YES cost $\le B^g_k$, NO cost $= B^g_k + k$, time $N^{C_0 A^k}$
-- statement:
--   There are absolute constants $A \ge 2$ and $C_0 > 0$, an effective dyadic cutoff $s_0$, and a deterministic algorithm with the following guarantee. Given a YES or NO source graph $G$ from Theorem 5.2, an integer $k \ge 1$, and a power of two $s_g \ge s_0$ with $N = s_g^4 \ge |V(G)|$, it produces an explicit total Boolean matrix $F_{G,k}$, square with power-of-two side length at least $N$, and the public integer
--   $$
--   B^g_k = d_{0,g} + k h_g, \qquad d_{0,g} = \log \mathrm{pow2}(64(L_g+1)) + 1,\quad L_g = \log N,\quad h_g = 10 \log N,
--   $$
--   such that
--   $$
--   \text{YES: } D(F_{G,k}) \le B^g_k, \qquad \text{NO: } D(F_{G,k}) = B^g_k + k .
--   $$
--   Its running time and full output length are at most $N^{C_0 A^k}$.
--
--   With $k$ fixed, this is the polynomial-time gap reduction from source graphs that, composed with Theorem 5.2, gives Theorem 1.1.
--
--   **Formalization Note** The algorithm is one Turing machine (published `CookPvsNP.TM`) that reads the encoding of $(G, k, s_g)$ and halts within $N^{C_0 A^k}$ steps with output exactly the encoding of $(F_{G,k}, B^g_k)$. The parameter conditions of Lemma F.3 are $s_g \ge s_0$ and $s_g^4 \ge n$ ($s_g$ dyadic). Inputs outside the promise are unconstrained.
--
--   Differences from the source:
--   - generalization: the fixed graph constants Δ, γ of Theorem 5.2, with A, C₀, s₀ depending only on the fixed source reduction → for every Δ ≥ 1 and γ > 0 there are A, C₀, s₀ and a machine; reason: the paper's pair (Δ, γ) is one instance
--   - generalization: a YES or NO source graph produced by Theorem 5.2 → every graph with the shape of Theorem 5.2 that is 3-colorable or γ-far from 3-colorable; reason: the graphs produced by Theorem 5.2 are among them
--   - reading: effective constants A, C₀ and "the parameter conditions of Lemma F.3" → natural numbers A ≥ 2, C₀ > 0 and a dyadic s₀ with the conditions s_g ≥ s₀, s_g⁴ ≥ |V(G)|; reason: a fixed number has no formal effectivity property; Lemma F.3 (p.69) states the conditions as every dyadic s ≥ max{n^{1/4}, s₀}
--   - encoding: explicit matrix, running time and binary output length → a CookPvsNP.TM run on encodeGapInput with output encodeTableNat F B, time and output length ≤ N^{C₀A^k}; reason: explicit injective encodings with polynomially related lengths
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 8.4, pp.36–37 (parameter conditions: Lemma F.3, p.69; h_g = 10 log N: Corollary 8.1, p.35)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_SrcGraph
import Definitions.Def_DetCCHard_pow2
import Definitions.Def_DetCCHard_CodeSym
import Definitions.Def_DetCCHard_encodeGraph

namespace DetCCHard

/-- **Theorem 8.4 (deterministic gap tables)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held
version sha256 ad552d13…a4a03, Theorem 8.4, pp.36–37, with the parameter conditions of
Lemma F.3, p.69, and `h_g = 10 log N` of Corollary 8.1, p.35). There are effective absolute
constants `A ≥ 2` and `C₀ > 0` and a deterministic algorithm with the following guarantee. Given a
YES or NO source graph `G` from Theorem 5.2, an integer `k ≥ 1`, and a power of two `s_g` such that
`N = s_g^4 ≥ |V(G)|` meets the parameter conditions of Lemma F.3 (`s_g ≥ s₀` for an effective
dyadic `s₀`), it produces an explicit total Boolean matrix `F_{G,k}` and the public integer
`B^g_k = d_{0,g} + k h_g` such that YES: `D(F_{G,k}) ≤ B^g_k` and NO: `D(F_{G,k}) = B^g_k + k`. Its
running time and full output length are at most `N^{C₀ A^k}`. The output is square with
power-of-two side length at least `N`. Here `d_{0,g} = log pow2(64(L_g + 1)) + 1`,
`L_g = log N`, and `h_g = 10 log N`.

**Formalization Note** The algorithm is one Turing machine (published `CookPvsNP.TM`) reading
`encodeGapInput G k s_g` and writing `encodeTableNat F B^g_k`; `RunsWithin` says it halts within
the stated number of steps with exactly that output. The constants `A`, `C₀`, `s₀` and the machine
are chosen after the graph-promise constants `Δ ≥ 1`, `γ > 0` (the paper fixes the pair from
Theorem 5.2, a special case) and before `G`, `k`, `s_g`. A source graph is any graph with the
shape of Theorem 5.2 that is YES or NO. Inputs outside the promise are unconstrained. Logarithms
are `Nat.log 2` of powers of two. -/
theorem theorem_8_4 :
    ∀ Δ : ℕ, 1 ≤ Δ → ∀ γ : ℚ, 0 < γ →
      ∃ (A C₀ s₀ : ℕ), 2 ≤ A ∧ 0 < C₀ ∧ (∃ e : ℕ, s₀ = 2 ^ e) ∧
        ∃ (Γ : Type) (_ : Fintype Γ) (ι₁ : CodeSym ↪ Γ) (ι₂ : CodeSym ↪ Γ)
          (M : CookPvsNP.TM Γ),
          ∀ G : SrcGraph, IsShape Δ G → (IsYes G ∨ IsNo γ G) →
          ∀ k : ℕ, 1 ≤ k → ∀ sg : ℕ, (∃ e : ℕ, sg = 2 ^ e) → s₀ ≤ sg → G.n ≤ sg ^ 4 →
            ∃ (j : ℕ) (F : Fin (2 ^ j) → Fin (2 ^ j) → Bool),
              sg ^ 4 ≤ 2 ^ j ∧
              RunsWithin M ι₁ ι₂ (encodeGapInput G k sg) ((sg ^ 4) ^ (C₀ * A ^ k))
                (encodeTableNat F (Nat.log 2 (pow2 (64 * (Nat.log 2 (sg ^ 4) + 1))) + 1 +
                  k * (10 * Nat.log 2 (sg ^ 4)))) ∧
              (encodeTableNat F (Nat.log 2 (pow2 (64 * (Nat.log 2 (sg ^ 4) + 1))) + 1 +
                  k * (10 * Nat.log 2 (sg ^ 4)))).length ≤ (sg ^ 4) ^ (C₀ * A ^ k) ∧
              (IsYes G → Dcost F ≤ Nat.log 2 (pow2 (64 * (Nat.log 2 (sg ^ 4) + 1))) + 1 +
                  k * (10 * Nat.log 2 (sg ^ 4))) ∧
              (IsNo γ G → Dcost F = Nat.log 2 (pow2 (64 * (Nat.log 2 (sg ^ 4) + 1))) + 1 +
                  k * (10 * Nat.log 2 (sg ^ 4)) + k) := by sorry

end DetCCHard
