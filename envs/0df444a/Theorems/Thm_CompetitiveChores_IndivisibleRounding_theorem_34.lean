-- Prove2me | Theorems.Thm_CompetitiveChores_IndivisibleRounding_theorem_34
-- name    : CompetitiveChores.IndivisibleRounding.theorem_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:45.776156+00:00
-- url     : https://prove2.me/theorems/f20adc1c-14fa-4f95-9f77-d656072154ec
-- title:
--   Theorem 34, p. 37 — a Pareto optimal indivisible allocation of chores that is weighted-EF¹₁ and weighted-Prop1
-- statement:
--   Pareto optimal and approximately fair division of indivisible chores (Theorem 34).
--
--   Let $n\ge1$ agents divide $m$ indivisible chores, with values $v\in\mathbb R^{n\times m}_{<0}$, and let $\beta\in\mathbb R^n_{>0}$ be any vector of weights. Then there is an indivisible allocation $z$ such that
--
--   1. $z$ is Pareto optimal in the divisible problem: its utility profile lies on the Pareto frontier,
--   $$u(z)\in\mathcal U^*(v),$$
--   the comparison being with all feasible fractional allocations;
--   2. $z$ is weighted-EF¹₁ with weights $\beta$ (Definition 32);
--   3. $z$ is weighted-Prop1 with weights $\beta$ (Definition 33).
--
--   Envy-free or proportional allocations of indivisible chores need not exist; the theorem shows that the two relaxations can always be achieved together with Pareto efficiency, with arbitrary entitlements $\beta$.
--
--   **Formalization Note** $n\ge1$ is added (with no agents and $m\ge1$ chores no allocation exists); $m=0$ is allowed. An indivisible allocation is a map $\sigma$ from chores to agents, and $u(z)$ is the utility profile of its 0/1 matrix. The second sentence of the theorem (strongly polynomial running time for fixed $n$ or $m$) is not formalized.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 37, Theorem 34

import Mathlib
import Definitions.Def_CompetitiveChores_IndivisibleRounding_Setting
import Definitions.Def_CompetitiveChores_IndivisibleRounding_Indivisible

namespace CompetitiveChores.IndivisibleRounding

/-- Theorem 34, p. 37: for any `v ∈ ℝ^{n×m}_{<0}` and weights `β ∈ ℝ^n_{>0}` there is an indivisible
allocation whose utility profile lies on the Pareto frontier `𝒰*(v)` of the divisible problem and which
is both weighted-EF¹₁ and weighted-Prop1 with weights `β`. -/
theorem theorem_34 {n m : ℕ} (hn : 0 < n) (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0)
    (β : Fin n → ℝ) (hβ : ∀ i, 0 < β i) :
    ∃ σ : Fin m → Fin n, CompetitiveChores.RichFamily.utilityProfile v (indicator σ) ∈ CompetitiveChores.RichFamily.paretoFrontier v ∧
      IsWeightedEF11 v β σ ∧ IsWeightedProp1 v β σ := by sorry

end CompetitiveChores.IndivisibleRounding
