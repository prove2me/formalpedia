-- Prove2me | Theorems.Thm_DRSubmodHull_lemma_5_20_t_nonincreasing
-- name    : DRSubmodHull.lemma_5_20_t_nonincreasing
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:57.204842+00:00
-- url     : https://prove2.me/theorems/d922a8fe-8850-4d22-a0a0-dc84a50c18d8
-- title:
--   Lemma 5.20 — $t(\delta,\bar z)$ is non-increasing along an output of Algorithm 2
-- statement:
--   Throughout, $\mathcal G=(\mathcal V,\mathcal A)$ is a directed rooted forest, $N\subseteq\mathcal V$ is the set of integer variables, and the upper bounds satisfy the paper's standing conditions: $u_i>0$ for all $i$, $u_i\in\mathbb Z$ for $i\in N$, and $u_i\le u_j$ for every arc $(i,j)$. As in the paper from p.8 on, Assumption 1 and Property 4.2 hold.
--
--   Let $\bar z\in\mathrm{conv}(\mathcal Z(\mathcal G,u))$ and let $\delta$ be a permutation returned by Algorithm 2 on $\bar z$. Then
--   $$
--   t(\delta,\bar z)_k\;\ge\;t(\delta,\bar z)_{k+1}\qquad\text{for all } k\in\{1,\dots,|\mathcal V|-1\}.
--   $$
--
--   With Lemmas 5.17 and 5.21 this makes the affine combination of Lemma 5.16 a convex combination.
--
--   Differences from the source:
--   - encoding: variables indexed 1, …, n + m with the n integer variables first (z ∈ ℤⁿ × ℝᵐ) → an arbitrary finite type V of coordinates and an arbitrary set N ⊆ V of integer coordinates; reason: relabelling of coordinates; same instances (N or its complement may be empty, as the paper allows)
--   - encoding: 𝒢 a directed rooted forest with arcs pointing away from the roots; 0 ≤ u ≤ ∞ reduced to u < ∞ (p.5) → arc relation with in-degree at most one and no directed cycle; u : V → ℝ; reason: on a finite vertex set the two forest notions coincide; finiteness of u is the paper's own reduction on p.5 and is assumed in every later section
--   - encoding: ch(ψ), the unique child of ψ ∈ Ψ (p.8) → child A ψ, a chosen out-neighbour of ψ; reason: Property 4.2 is a hypothesis, so ψ has exactly one child and child A ψ is it
--   - encoding: permutations δ = (δ(1), …, δ(|𝒱|)); index 0 for 'no ascendant' with u₀ = z₀ = 0 → δ : Fin |V| ≃ V (Lean position m is the paper's position m + 1); i△(𝒮) : Option V with none ↦ 0; reason: Lean convention; t(δ, z)_k keeps the paper's 1-based k, with t₀ = 1 and t_{|𝒱|+1} = 0
--   - reading: 'the output' of Algorithm 2, which breaks ties arbitrarily → every δ satisfying IsPermFinderOutput (every tie-break); reason: the paper fixes no tie-break, so its claim is about each possible output; this is the stronger of the two readings
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, Lemma 5.20, p.22

import Mathlib
import Definitions.Def_DRSubmodHull_IsPermFinderOutput

set_option autoImplicit false

namespace DRSubmodHull

/-- **Lemma 5.20** (Yu, Küçükyavuz, arXiv:2211.07726v2, §5, p.22). Let `δ` be the permutation
returned by Algorithm 2 given `𝒢`, `u` and `z̄ ∈ conv(𝒵(𝒢, u))`. For all
`k ∈ {1, …, |𝒱| − 1}`, `t(δ, z̄)_k ≥ t(δ, z̄)_{k+1}`.

Hypotheses: the standing conditions (pp.4–5), Assumption 1 and Property 4.2 (p.8).

**Formalization Note.** "The permutation returned" is every output of Algorithm 2 (every
tie-break). The range `Finset.Icc 1 (|V| − 1)` is the paper's `{1, …, |𝒱| − 1}` (empty when
`|𝒱| ≤ 1`). -/
theorem lemma_5_20_t_nonincreasing {V : Type*} [Fintype V]
    (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (hstd : StandingConditions A N u) (hA1 : Assumption1 A N u) (hP42 : Property42 A N u)
    (zbar : V → ℝ) (hz : zbar ∈ convexHull ℝ (Zset A N u))
    (δ : Fin (Fintype.card V) ≃ V) (hδ : IsPermFinderOutput A N u zbar δ) :
    ∀ k ∈ Finset.Icc 1 (Fintype.card V - 1), tval A N u δ zbar (k + 1) ≤ tval A N u δ zbar k := by sorry

end DRSubmodHull
