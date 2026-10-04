-- Prove2me | Theorems.Thm_BookProof_FriedrichsExtension_unbounded_friedrichs_example
-- name    : BookProof.FriedrichsExtension.unbounded_friedrichs_example
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T13:15:35.613874+00:00
-- url     : https://prove2.me/theorems/369face2-3b1a-47bf-9bc0-623bf5e414e8
-- title:
--   The Lean 4 theorem `unbounded_friedrichs_example` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `unbounded_friedrichs_example` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsExtension.lean

-- Generated from ChapterFriedrichsExtension.lean — theorem BookProof.FriedrichsExtension.unbounded_friedrichs_example
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [CompleteSpace F]



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
open scoped InnerProductSpace ENNReal lp

theorem BookProof.FriedrichsExtension.unbounded_friedrichs_example :
    (∃ (Dom : Submodule ℂ (ℓ²(ℕ, ℂ))) (A : Dom →ₗ[ℂ] ℓ²(ℕ, ℂ)),
        IsPositiveSelfAdjointExtension ell2ExampleMatrix A) ∧
      ∀ C : ℝ, ∃ x : finiteModeDomain ell2Basis,
        C * ‖(x : ℓ²(ℕ, ℂ))‖ < ‖ell2ExampleMatrix x‖ := by sorry
