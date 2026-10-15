-- Prove2me | Theorems.Thm_CompetitiveChores_RichFamily_theorem_9
-- name    : CompetitiveChores.RichFamily.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:27.660986+00:00
-- url     : https://prove2.me/theorems/f6225757-010f-46a6-909a-982727a7030b
-- title:
--   Theorem 9 — first and second welfare theorems for chores
-- statement:
--   Let $v\in\mathbb R^{n\times m}_{<0}$. Then:
--   1. (*first welfare theorem*) for every vector of budgets $b\in\mathbb R^n_{<0}$, every allocation that is competitive for $b$ is Pareto optimal;
--   2. (*second welfare theorem*) for every Pareto optimal allocation $z$ with $u(z)\in\mathbb R^n_{<0}$ there is a vector of budgets $b\in\mathbb R^n_{<0}$ such that $z$ is competitive for $b$.
--
--   The first item places every competitive utility profile on the Pareto frontier; the second is the paper's route to the agent–item parity of MWW graphs (Lemma 22).
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 14, §2.3, Theorem 9

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_CompetitiveChores_RichFamily_Graphs

namespace CompetitiveChores.RichFamily

variable {n m : ℕ}

/-- Theorem 9 (Welfare theorems), p. 14: (1) for every budget vector `b ∈ ℝ^n_{<0}`, any competitive
allocation is Pareto optimal; (2) for any Pareto optimal allocation `z` with `u(z) ∈ ℝ^n_{<0}` there is
a budget vector `b ∈ ℝ^n_{<0}` for which `z` is competitive. -/
theorem theorem_9 (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0) :
    (∀ b : Fin n → ℝ, (∀ i, b i < 0) → ∀ z, IsCompetitive v b z → IsParetoOptimal v z) ∧
      ∀ z, IsParetoOptimal v z → (∀ i, utilityProfile v z i < 0) →
        ∃ b : Fin n → ℝ, (∀ i, b i < 0) ∧ IsCompetitive v b z := by sorry

end CompetitiveChores.RichFamily
