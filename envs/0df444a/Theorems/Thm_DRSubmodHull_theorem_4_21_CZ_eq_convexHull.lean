-- Prove2me | Theorems.Thm_DRSubmodHull_theorem_4_21_CZ_eq_convexHull
-- name    : DRSubmodHull.theorem_4_21_CZ_eq_convexHull
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:16.507234+00:00
-- url     : https://prove2.me/theorems/2637872a-062d-40c7-9041-222f4f161173
-- title:
--   Theorem 4.21 — $\mathcal{CZ}=\mathrm{conv}(\mathcal Z(\mathcal G,u))$
-- statement:
--   Throughout, $\mathcal G=(\mathcal V,\mathcal A)$ is a directed rooted forest, $N\subseteq\mathcal V$ is the set of integer variables, and the upper bounds satisfy the paper's standing conditions: $u_i>0$ for all $i$, $u_i\in\mathbb Z$ for $i\in N$, and $u_i\le u_j$ for every arc $(i,j)$. As in the paper from p.8 on, Assumption 1 and Property 4.2 hold.
--
--   The box, monotonicity and MIR inequalities (6a)–(6c) describe the convex hull of the mixed-integer set:
--   $$
--   \mathcal{CZ}=\mathrm{conv}\big(\mathcal Z(\mathcal G,u)\big).
--   $$
--
--   The variable part $z$ of the convex hull of the epigraph is therefore described by $\mathcal{CZ}$ (Theorem 7.1).
--
--   **Formalization Note** $\mathrm{conv}$ is the convex hull (finite convex combinations), not its closure.
--
--   Differences from the source:
--   - encoding: variables indexed 1, …, n + m with the n integer variables first (z ∈ ℤⁿ × ℝᵐ) → an arbitrary finite type V of coordinates and an arbitrary set N ⊆ V of integer coordinates; reason: relabelling of coordinates; same instances (N or its complement may be empty, as the paper allows)
--   - encoding: 𝒢 a directed rooted forest with arcs pointing away from the roots; 0 ≤ u ≤ ∞ reduced to u < ∞ (p.5) → arc relation with in-degree at most one and no directed cycle; u : V → ℝ; reason: on a finite vertex set the two forest notions coincide; finiteness of u is the paper's own reduction on p.5 and is assumed in every later section
--   - encoding: ch(ψ), the unique child of ψ ∈ Ψ (p.8) → child A ψ, a chosen out-neighbour of ψ; reason: Property 4.2 is a hypothesis, so ψ has exactly one child and child A ψ is it
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, Theorem 4.21, p.13

import Mathlib
import Definitions.Def_DRSubmodHull_CZ

set_option autoImplicit false

namespace DRSubmodHull

/-- **Theorem 4.21** (Yu, Küçükyavuz, arXiv:2211.07726v2, §4, p.13). The set `𝒞𝒵` defined by
(6a)–(6c) is `conv(𝒵(𝒢, u))`.

Hypotheses: the standing conditions (pp.4–5), Assumption 1 and Property 4.2 (p.8).

**Formalization Note.** `conv` is Mathlib's `convexHull ℝ` (finite convex combinations), not its
closure. -/
theorem theorem_4_21_CZ_eq_convexHull {V : Type*} [Fintype V]
    (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (hstd : StandingConditions A N u) (hA1 : Assumption1 A N u) (hP42 : Property42 A N u) :
    CZ A N u = convexHull ℝ (Zset A N u) := by sorry

end DRSubmodHull
