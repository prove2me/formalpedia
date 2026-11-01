-- Prove2me | Theorems.Thm_DRSubmodHull_corollary_4_20_extreme_points_CZ
-- name    : DRSubmodHull.corollary_4_20_extreme_points_CZ
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:26:23.897983+00:00
-- url     : https://prove2.me/theorems/c1505db2-43e0-43a1-82fc-292867d1503c
-- title:
--   Corollary 4.20 — the extreme points of $\mathcal{CZ}$ are exactly the points $P(\mathcal S)$
-- statement:
--   Throughout, $\mathcal G=(\mathcal V,\mathcal A)$ is a directed rooted forest, $N\subseteq\mathcal V$ is the set of integer variables, and the upper bounds satisfy the paper's standing conditions: $u_i>0$ for all $i$, $u_i\in\mathbb Z$ for $i\in N$, and $u_i\le u_j$ for every arc $(i,j)$. As in the paper from p.8 on, Assumption 1 and Property 4.2 hold.
--
--   The extreme points of the polyhedron $\mathcal{CZ}$ defined by (6a)–(6c) are exactly the points $P(\mathcal S)$, $\mathcal S\subseteq\mathcal V$, of (9):
--   $$
--   \operatorname{ext}(\mathcal{CZ})=\{P(\mathcal S):\mathcal S\subseteq\mathcal V\}.
--   $$
--
--   This explicit vertex description is what the DR inequalities are built from.
--
--   Differences from the source:
--   - encoding: variables indexed 1, …, n + m with the n integer variables first (z ∈ ℤⁿ × ℝᵐ) → an arbitrary finite type V of coordinates and an arbitrary set N ⊆ V of integer coordinates; reason: relabelling of coordinates; same instances (N or its complement may be empty, as the paper allows)
--   - encoding: 𝒢 a directed rooted forest with arcs pointing away from the roots; 0 ≤ u ≤ ∞ reduced to u < ∞ (p.5) → arc relation with in-degree at most one and no directed cycle; u : V → ℝ; reason: on a finite vertex set the two forest notions coincide; finiteness of u is the paper's own reduction on p.5 and is assumed in every later section
--   - encoding: ch(ψ), the unique child of ψ ∈ Ψ (p.8) → child A ψ, a chosen out-neighbour of ψ; reason: Property 4.2 is a hypothesis, so ψ has exactly one child and child A ψ is it
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, Corollary 4.20, p.13

import Mathlib
import Definitions.Def_DRSubmodHull_Ppt

set_option autoImplicit false

namespace DRSubmodHull

/-- **Corollary 4.20** (Yu, Küçükyavuz, arXiv:2211.07726v2, §4, p.13). The extreme points of
`𝒞𝒵`, defined by (6a)–(6c), are exactly `{P(𝒮)}_{𝒮 ⊆ 𝒱}` given by (9).

Hypotheses: the standing conditions (pp.4–5), Assumption 1 and Property 4.2 (p.8). -/
theorem corollary_4_20_extreme_points_CZ {V : Type*} [Fintype V]
    (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (hstd : StandingConditions A N u) (hA1 : Assumption1 A N u) (hP42 : Property42 A N u) :
    Set.extremePoints ℝ (CZ A N u) = Set.range (Ppt A N u) := by sorry

end DRSubmodHull
