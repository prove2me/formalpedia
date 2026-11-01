-- Prove2me | Theorems.Thm_DRSubmodHull_algorithm_2_output_valid
-- name    : DRSubmodHull.algorithm_2_output_valid
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:42.232121+00:00
-- url     : https://prove2.me/theorems/827cfd09-dda9-412d-a6d8-f2c56683a9af
-- title:
--   Algorithm 2 (§5) — Permutation_Finder has an output, and every output is a valid permutation
-- statement:
--   Throughout, $\mathcal G=(\mathcal V,\mathcal A)$ is a directed rooted forest, $N\subseteq\mathcal V$ is the set of integer variables, and the upper bounds satisfy the paper's standing conditions: $u_i>0$ for all $i$, $u_i\in\mathbb Z$ for $i\in N$, and $u_i\le u_j$ for every arc $(i,j)$. As in the paper from p.8 on, Assumption 1 and Property 4.2 hold.
--
--   Let $\bar z\in\mathrm{conv}(\mathcal Z(\mathcal G,u))$. Then Algorithm 2 (Permutation_Finder) run on $\bar z$ produces a full permutation of $\mathcal V$, and every permutation it can produce (for every way of breaking ties) is valid in the sense of Definition 5.2.
--
--   The paper states this after Algorithm 2 on p.19, from Observation 5.7 and the exactness of Algorithm 1.
--
--   Differences from the source:
--   - encoding: variables indexed 1, …, n + m with the n integer variables first (z ∈ ℤⁿ × ℝᵐ) → an arbitrary finite type V of coordinates and an arbitrary set N ⊆ V of integer coordinates; reason: relabelling of coordinates; same instances (N or its complement may be empty, as the paper allows)
--   - encoding: 𝒢 a directed rooted forest with arcs pointing away from the roots; 0 ≤ u ≤ ∞ reduced to u < ∞ (p.5) → arc relation with in-degree at most one and no directed cycle; u : V → ℝ; reason: on a finite vertex set the two forest notions coincide; finiteness of u is the paper's own reduction on p.5 and is assumed in every later section
--   - encoding: ch(ψ), the unique child of ψ ∈ Ψ (p.8) → child A ψ, a chosen out-neighbour of ψ; reason: Property 4.2 is a hypothesis, so ψ has exactly one child and child A ψ is it
--   - encoding: permutations δ = (δ(1), …, δ(|𝒱|)); index 0 for 'no ascendant' with u₀ = z₀ = 0 → δ : Fin |V| ≃ V (Lean position m is the paper's position m + 1); i△(𝒮) : Option V with none ↦ 0; reason: Lean convention; t(δ, z)_k keeps the paper's 1-based k, with t₀ = 1 and t_{|𝒱|+1} = 0
--   - reading: 'the output' of Algorithm 2, which breaks ties arbitrarily → every δ satisfying IsPermFinderOutput (every tie-break); reason: the paper fixes no tie-break, so its claim is about each possible output; this is the stronger of the two readings
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, §5, p.19, the paragraph after Algorithm 2

import Mathlib
import Definitions.Def_DRSubmodHull_IsPermFinderOutput

set_option autoImplicit false

namespace DRSubmodHull

/-- **Algorithm 2 returns a valid full permutation** (Yu, Küçükyavuz, arXiv:2211.07726v2, §5, p.19,
the paragraph after Algorithm 2): "By Observation 5.7, `Δ ≠ ∅` in every iteration, and the partial
permutation `δᵏ` for every `k ∈ {1, 2, …, |𝒱|}` is valid. Therefore, the output from Algorithm 2 is
a valid and full permutation of `𝒱`."

For `z̄ ∈ conv(𝒵(𝒢, u))` (the input of Algorithm 2), Algorithm 2 has an output, and every output
(every tie-break) is a valid permutation.

Hypotheses: the standing conditions (pp.4–5), Assumption 1 and Property 4.2 (p.8). -/
theorem algorithm_2_output_valid {V : Type*} [Fintype V]
    (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (hstd : StandingConditions A N u) (hA1 : Assumption1 A N u) (hP42 : Property42 A N u)
    (zbar : V → ℝ) (hz : zbar ∈ convexHull ℝ (Zset A N u)) :
    (∃ δ : Fin (Fintype.card V) ≃ V, IsPermFinderOutput A N u zbar δ) ∧
      ∀ δ : Fin (Fintype.card V) ≃ V, IsPermFinderOutput A N u zbar δ →
        IsValidPerm A N u δ := by sorry

end DRSubmodHull
