-- Prove2me | Theorems.Thm_D1Bound5_mainStatement_iff_three_ordered_cases
-- name    : D1Bound5.mainStatement_iff_three_ordered_cases
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:28:15.264639+00:00
-- url     : https://prove2.me/theorems/a0573729-e043-4d90-ab61-249b0e305dfc
-- title:
--   The full-ring bound reduced to three ordered cases
-- statement:
--   The assertion that every finite Diophantine set in the full ring of integers of every imaginary quadratic number field has cardinality at most five is equivalent to the following three exclusions. For every such field K, every complex embedding of K, and every Diophantine sextuple of algebraic integers ordered by nondecreasing complex absolute value, each of the following conditions is impossible:
--
--   1. The first absolute value is at least 3.
--   2. The first absolute value is below 3 and the second is at least 3.
--   3. The second absolute value is below 3.
--
--   The equivalence holds for the full rings of integers, including half-integral bases, and permits ties in absolute value.
-- source:
--   D1Bound5/MainCaseReduction.lean, D1Bound5.mainStatement_iff_three_ordered_cases, lines 92-118; exact source SHA-256 94580cd4f5977bc9f503aba3da8004380cecfe272766c2d856a70706a14c5d2b. Original project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_MainStatement
import Mathlib.Analysis.Complex.Basic
import Lean.Elab.Tactic.Omega

open D1Bound5
open scoped NumberField
universe u

theorem D1Bound5.mainStatement_iff_three_ordered_cases :
    MainStatement.{u} ↔
      ∀ (K : Type u) [Field K] [NumberField K]
        [NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 →
        ∀ phi : K →+* ℂ,
          (∀ t : Fin 6 → 𝓞 K, IsD1Tuple t →
            Monotone (fun i => ‖phi (t i : K)‖) →
            3 ≤ ‖phi (t 0 : K)‖ → False) ∧
          (∀ t : Fin 6 → 𝓞 K, IsD1Tuple t →
            Monotone (fun i => ‖phi (t i : K)‖) →
            ‖phi (t 0 : K)‖ < 3 → 3 ≤ ‖phi (t 1 : K)‖ → False) ∧
          (∀ t : Fin 6 → 𝓞 K, IsD1Tuple t →
            Monotone (fun i => ‖phi (t i : K)‖) →
            ‖phi (t 1 : K)‖ < 3 → False) := by sorry
