-- Prove2me | Theorems.Thm_CompetitiveChores_RichFamily_corollary_10
-- name    : CompetitiveChores.RichFamily.corollary_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:32.947424+00:00
-- url     : https://prove2.me/theorems/c0f56483-5cd3-4a23-90d6-763f3099f29c
-- title:
--   Corollary 10 — Pareto indifference: every feasible allocation with a competitive utility profile is competitive
-- statement:
--   Let $v\in\mathbb R^{n\times m}_{<0}$ and $b\in\mathbb R^n_{<0}$. If $u$ is a competitive utility profile for the budgets $b$, then every feasible allocation $z$ with $u(z)=u$ is competitive for $b$.
--
--   Whether an allocation is competitive therefore depends only on its utility profile. This is what allows the enumeration to work with consumption graphs: any feasible allocation realizing a competitive profile may be used in place of the original one.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 14, §2.3, Corollary 10

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

namespace CompetitiveChores.RichFamily

variable {n m : ℕ}

/-- Corollary 10 (Pareto indifference), p. 14: if `u` is a competitive utility profile, then any
feasible allocation `z` with `u = u(z)` is competitive. -/
theorem corollary_10 (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0) (b : Fin n → ℝ)
    (hb : ∀ i, b i < 0) (u : Fin n → ℝ) (hu : IsCompetitiveProfile v b u)
    (z : Fin n → Fin m → ℝ) (hz : IsFeasible z) (hzu : utilityProfile v z = u) :
    IsCompetitive v b z := by sorry

end CompetitiveChores.RichFamily
