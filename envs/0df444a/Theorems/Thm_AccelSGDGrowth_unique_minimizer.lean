-- Prove2me | Theorems.Thm_AccelSGDGrowth_unique_minimizer
-- name    : AccelSGDGrowth.unique_minimizer
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:26.008948+00:00
-- url     : https://prove2.me/theorems/5b3f6048-f8b4-479a-8cea-c5ff9c314fe7
-- title:
--   The unique minimizer $x_\star$ of $f\in\mathcal F(m,\mathcal L)$
-- statement:
--   Let $0<m\le\mathcal L$ and $f\in\mathcal F(m,\mathcal L)$. Then $f$ has exactly one global minimizer $x_\star\in\mathbb R^d$:
--   $$
--   \exists!\,x_\star\in\mathbb R^d:\quad f(x_\star)\le f(x)\ \text{ for all } x\in\mathbb R^d .
--   $$
--   The paper writes $x_\star=\arg\min f(x)$; this justifies binding $x_\star$ by the minimizer property in every other statement of the mission.
--
--   Differences from the source:
--   - encoding: f ∈ F(m, L), m-strongly convex with condition number κ = L/m → 0 < m and m ≤ L as hypotheses; reason: strong convexity and κ = L/m need m > 0; (1.2) forces m ≤ L whenever d ≥ 1, so only the trivial case d = 0 is affected
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, p.2 ('x⋆ = arg min f(x) denotes the unique minimizer of f')

import Definitions.Def_AccelSGDGrowth_ClassF

namespace AccelSGDGrowth

/-- Chen, Na, Kolar, arXiv:2006.06782v4, p.2: "Here, x⋆ = arg min f(x) denotes the unique
minimizer of f." For `f ∈ F(m, L)` with `0 < m ≤ L`, `f` has exactly one global minimizer on `ℝ^d`.

**Formalization Note.** The minimizer is expressed with `IsMinOn f Set.univ`; this item justifies
binding `x⋆` by that predicate in the other statements of the mission. -/
theorem unique_minimizer {d : ℕ} {m L : ℝ} (hm : 0 < m) (hmL : m ≤ L)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ClassF m L f) :
    ∃! xstar : EuclideanSpace ℝ (Fin d), IsMinOn f Set.univ xstar := by sorry

end AccelSGDGrowth
