-- Prove2me | Theorems.Thm_DRSubmodHull_lemma_5_16_affine_combination
-- name    : DRSubmodHull.lemma_5_16_affine_combination
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:08.2133+00:00
-- url     : https://prove2.me/theorems/bd9e6f8f-8d8b-45a1-a298-069023688b7e
-- title:
--   Lemma 5.16 — every $\bar z$ is an affine combination of the points $P(\delta,k)$
-- statement:
--   Throughout, $\mathcal G=(\mathcal V,\mathcal A)$ is a directed rooted forest, $N\subseteq\mathcal V$ is the set of integer variables, and the upper bounds satisfy the paper's standing conditions: $u_i>0$ for all $i$, $u_i\in\mathbb Z$ for $i\in N$, and $u_i\le u_j$ for every arc $(i,j)$. As in the paper from p.8 on, Assumption 1 and Property 4.2 hold.
--
--   For every valid permutation $\delta$ and every $\bar z\in\mathbb R^{\mathcal V}$,
--   $$
--   \bar z=\sum_{k=0}^{|\mathcal V|}\big[t(\delta,\bar z)_k-t(\delta,\bar z)_{k+1}\big]\,P(\delta,k),
--   \qquad \sum_{k=0}^{|\mathcal V|}\big[t(\delta,\bar z)_k-t(\delta,\bar z)_{k+1}\big]=1,
--   $$
--   with $t(\delta,\bar z)_0=1$ and $t(\delta,\bar z)_{|\mathcal V|+1}=0$.
--
--   The coefficients are linear in $\bar z$; for the permutation found by Algorithm 2 they are non-negative (Proposition 5.22).
--
--   Differences from the source:
--   - encoding: variables indexed 1, …, n + m with the n integer variables first (z ∈ ℤⁿ × ℝᵐ) → an arbitrary finite type V of coordinates and an arbitrary set N ⊆ V of integer coordinates; reason: relabelling of coordinates; same instances (N or its complement may be empty, as the paper allows)
--   - encoding: 𝒢 a directed rooted forest with arcs pointing away from the roots; 0 ≤ u ≤ ∞ reduced to u < ∞ (p.5) → arc relation with in-degree at most one and no directed cycle; u : V → ℝ; reason: on a finite vertex set the two forest notions coincide; finiteness of u is the paper's own reduction on p.5 and is assumed in every later section
--   - encoding: ch(ψ), the unique child of ψ ∈ Ψ (p.8) → child A ψ, a chosen out-neighbour of ψ; reason: Property 4.2 is a hypothesis, so ψ has exactly one child and child A ψ is it
--   - encoding: permutations δ = (δ(1), …, δ(|𝒱|)); index 0 for 'no ascendant' with u₀ = z₀ = 0 → δ : Fin |V| ≃ V (Lean position m is the paper's position m + 1); i△(𝒮) : Option V with none ↦ 0; reason: Lean convention; t(δ, z)_k keeps the paper's 1-based k, with t₀ = 1 and t_{|𝒱|+1} = 0
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, Lemma 5.16, p.19

import Mathlib
import Definitions.Def_DRSubmodHull_drRHS

set_option autoImplicit false

namespace DRSubmodHull

/-- **Lemma 5.16** (Yu, Küçükyavuz, arXiv:2211.07726v2, §5, p.19). Any `z̄ ∈ ℝ^{|𝒱|}` can be written
as an affine combination of `{P(δ, k)}_{k=0}^{|𝒱|}` for any valid `δ ∈ 𝔖(𝒱)`, namely
`z̄ = ∑_{k=0}^{|𝒱|} [t(δ, z̄)_k − t(δ, z̄)_{k+1}] P(δ, k)`
(and the coefficients sum to `1`).

Hypotheses: the standing conditions (pp.4–5), Assumption 1 and Property 4.2 (p.8).

**Formalization Note.** `P(δ, k) = P(𝒯^{δ,k})`; `t(δ, z̄)₀ = 1` and `t(δ, z̄)_{|𝒱|+1} = 0` (p.16)
are built into `tval`. -/
theorem lemma_5_16_affine_combination {V : Type*} [Fintype V]
    (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (hstd : StandingConditions A N u) (hA1 : Assumption1 A N u) (hP42 : Property42 A N u)
    (δ : Fin (Fintype.card V) ≃ V) (hδ : IsValidPerm A N u δ) (zbar : V → ℝ) :
    zbar = ∑ k ∈ Finset.range (Fintype.card V + 1),
        (tval A N u δ zbar k - tval A N u δ zbar (k + 1)) • Ppt A N u (Tset δ k) ∧
      ∑ k ∈ Finset.range (Fintype.card V + 1),
        (tval A N u δ zbar k - tval A N u δ zbar (k + 1)) = 1 := by sorry

end DRSubmodHull
