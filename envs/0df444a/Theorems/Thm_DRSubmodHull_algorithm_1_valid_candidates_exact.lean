-- Prove2me | Theorems.Thm_DRSubmodHull_algorithm_1_valid_candidates_exact
-- name    : DRSubmodHull.algorithm_1_valid_candidates_exact
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:54.159148+00:00
-- url     : https://prove2.me/theorems/d7999be2-7492-47a2-8950-0460e245e3e5
-- title:
--   Algorithm 1 (§5) — Valid_Candidates returns exactly the valid one-step extensions
-- statement:
--   Throughout, $\mathcal G=(\mathcal V,\mathcal A)$ is a directed rooted forest, $N\subseteq\mathcal V$ is the set of integer variables, and the upper bounds satisfy the paper's standing conditions: $u_i>0$ for all $i$, $u_i\in\mathbb Z$ for $i\in N$, and $u_i\le u_j$ for every arc $(i,j)$. As in the paper from p.8 on, Assumption 1 and Property 4.2 hold.
--
--   Let $\delta'=(\delta(1),\dots,\delta(k))$ be a valid partial permutation of $\mathcal V'\subseteq\mathcal V$ with $|\mathcal V'|=k<|\mathcal V|$. The set $\Delta$ returned by Algorithm 1 consists exactly of the vertices $i\in\mathcal V\setminus\mathcal V'$ for which $(\delta(1),\dots,\delta(k),i)$ is a valid partial permutation:
--   $$
--   \Delta=\{\,i\in\mathcal V\setminus\mathcal V' : (\delta',i)\ \text{is valid}\,\}.
--   $$
--
--   The paper states this on p.15 in two sentences: $\Delta$ contains all such $i$, and Algorithm 1 excludes $i$ exactly when $(\delta',i)$ is not valid. Hence Algorithm 2 only builds valid permutations.
--
--   Differences from the source:
--   - encoding: variables indexed 1, …, n + m with the n integer variables first (z ∈ ℤⁿ × ℝᵐ) → an arbitrary finite type V of coordinates and an arbitrary set N ⊆ V of integer coordinates; reason: relabelling of coordinates; same instances (N or its complement may be empty, as the paper allows)
--   - encoding: 𝒢 a directed rooted forest with arcs pointing away from the roots; 0 ≤ u ≤ ∞ reduced to u < ∞ (p.5) → arc relation with in-degree at most one and no directed cycle; u : V → ℝ; reason: on a finite vertex set the two forest notions coincide; finiteness of u is the paper's own reduction on p.5 and is assumed in every later section
--   - encoding: ch(ψ), the unique child of ψ ∈ Ψ (p.8) → child A ψ, a chosen out-neighbour of ψ; reason: Property 4.2 is a hypothesis, so ψ has exactly one child and child A ψ is it
--   - encoding: partial permutations δ′ ∈ 𝔖(𝒱′), 𝒱′ ⊆ 𝒱 → lists of vertices; valid iff equal to a prefix of a valid permutation (Definition 5.6); reason: a valid partial permutation is repetition-free, so the list is δ′; same instances
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, §5, p.15, the claim introducing Algorithm 1 and the paragraph after it

import Mathlib
import Definitions.Def_DRSubmodHull_IsPermFinderOutput

set_option autoImplicit false

namespace DRSubmodHull

/-- **Algorithm 1 is exact** (Yu, Küçükyavuz, arXiv:2211.07726v2, §5, p.15, the claim introducing
Algorithm 1 and the paragraph after it). Let `δ′ = (δ(1), …, δ(k)) ∈ 𝔖(𝒱′)` with
`|𝒱′| = k < |𝒱|` be a valid partial permutation. The set `Δ` returned by Algorithm 1
`Valid_Candidates` consists exactly of the `i ∈ 𝒱 \ 𝒱′` such that `(δ(1), …, δ(k), i)` is valid.

Hypotheses: the standing conditions (pp.4–5), Assumption 1 and Property 4.2 (p.8).

**Formalization Note.** Partial permutations are lists without repetition; validity is
Definition 5.6 (`IsValidPartialPerm`). Both inclusions are stated: the paper's sentences say that
`Δ` contains every valid extension and that Algorithm 1 excludes `i` exactly when the extension
is not valid. -/
theorem algorithm_1_valid_candidates_exact {V : Type*} [Fintype V]
    (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (hstd : StandingConditions A N u) (hA1 : Assumption1 A N u) (hP42 : Property42 A N u)
    (L : List V) (hL : IsValidPartialPerm A N u L) (hlen : L.length < Fintype.card V) :
    validCandidates A N u L = {i | i ∉ L ∧ IsValidPartialPerm A N u (L ++ [i])} := by sorry

end DRSubmodHull
