-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_isOpen_real_eq_iUnion_intervals
-- name    : AssumptionsOfPhysics.isOpen_real_eq_iUnion_intervals
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T16:02:01.684986+00:00
-- url     : https://prove2.me/theorems/9e5efeba-8a28-4cbf-8986-3c57917d3fae
-- title:
--   Open sets of reals are countable unions of open intervals
-- statement:
--   Every set $U$ in the standard topology on $\mathbb R$ is a countable union $U=\bigcup_{i=1}^\infty(a_i,b_i)$ of open intervals with $a_i,b_i\in\mathbb R\cup\{-\infty,+\infty\}$.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 3 (pp. 169–195), Proposition 3.56, p. 192

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

namespace AssumptionsOfPhysics
theorem isOpen_real_eq_iUnion_intervals (U : Set ℝ)
    (hU : @IsOpen ℝ (TopologicalSpace.generateFrom
      {S : Set ℝ | ∃ a b : ℚ, S = Set.Ioo (a : ℝ) (b : ℝ)}) U) :
    ∃ a b : ℕ → EReal, U = ⋃ i, {x : ℝ | a i < (x : EReal) ∧ (x : EReal) < b i} := by sorry
end AssumptionsOfPhysics
