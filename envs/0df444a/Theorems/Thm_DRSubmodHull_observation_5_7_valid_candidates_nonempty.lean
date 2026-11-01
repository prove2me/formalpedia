-- Prove2me | Theorems.Thm_DRSubmodHull_observation_5_7_valid_candidates_nonempty
-- name    : DRSubmodHull.observation_5_7_valid_candidates_nonempty
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:46.057965+00:00
-- url     : https://prove2.me/theorems/e7be6271-9c80-449e-b790-c40d4af7589b
-- title:
--   Observation 5.7 — Valid_Candidates is non-empty
-- statement:
--   Throughout, $\mathcal G=(\mathcal V,\mathcal A)$ is a directed rooted forest, $N\subseteq\mathcal V$ is the set of integer variables, and the upper bounds satisfy the paper's standing conditions: $u_i>0$ for all $i$, $u_i\in\mathbb Z$ for $i\in N$, and $u_i\le u_j$ for every arc $(i,j)$. As in the paper from p.8 on, Assumption 1 and Property 4.2 hold.
--
--   Let $\delta'$ be a valid partial permutation of $\mathcal V'\subsetneq\mathcal V$. Then the output $\Delta$ of Algorithm 1 on $\delta'$ is non-empty.
--
--   So Algorithm 2 can always extend its current partial permutation.
--
--   Differences from the source:
--   - encoding: variables indexed 1, …, n + m with the n integer variables first (z ∈ ℤⁿ × ℝᵐ) → an arbitrary finite type V of coordinates and an arbitrary set N ⊆ V of integer coordinates; reason: relabelling of coordinates; same instances (N or its complement may be empty, as the paper allows)
--   - encoding: 𝒢 a directed rooted forest with arcs pointing away from the roots; 0 ≤ u ≤ ∞ reduced to u < ∞ (p.5) → arc relation with in-degree at most one and no directed cycle; u : V → ℝ; reason: on a finite vertex set the two forest notions coincide; finiteness of u is the paper's own reduction on p.5 and is assumed in every later section
--   - encoding: ch(ψ), the unique child of ψ ∈ Ψ (p.8) → child A ψ, a chosen out-neighbour of ψ; reason: Property 4.2 is a hypothesis, so ψ has exactly one child and child A ψ is it
--   - encoding: partial permutations δ′ ∈ 𝔖(𝒱′), 𝒱′ ⊆ 𝒱 → lists of vertices; valid iff equal to a prefix of a valid permutation (Definition 5.6); reason: a valid partial permutation is repetition-free, so the list is δ′; same instances
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, Observation 5.7, p.15

import Mathlib
import Definitions.Def_DRSubmodHull_IsPermFinderOutput

set_option autoImplicit false

namespace DRSubmodHull

/-- **Observation 5.7** (Yu, Küçükyavuz, arXiv:2211.07726v2, §5, p.15). The output `Δ` from
Algorithm 1 is non-empty when `𝒱′ ⊊ 𝒱` (for a valid partial permutation `δ′ ∈ 𝔖(𝒱′)`, the input
of Algorithm 1).

Hypotheses: the standing conditions (pp.4–5), Assumption 1 and Property 4.2 (p.8).

**Formalization Note.** `𝒱′ ⊊ 𝒱` is `L.length < |V|` for the repetition-free list `L`. -/
theorem observation_5_7_valid_candidates_nonempty {V : Type*} [Fintype V]
    (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (hstd : StandingConditions A N u) (hA1 : Assumption1 A N u) (hP42 : Property42 A N u)
    (L : List V) (hL : IsValidPartialPerm A N u L) (hlen : L.length < Fintype.card V) :
    (validCandidates A N u L).Nonempty := by sorry

end DRSubmodHull
