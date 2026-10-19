-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_isSemibounded_of_isPositive_shift
-- name    : BookProof.FriedrichsCanonical.isSemibounded_of_isPositive_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:38:40.729677+00:00
-- url     : https://prove2.me/theorems/687660ff-6d54-4084-b3e5-0b1366cdc2df
-- title:
--   `BookProof.FriedrichsCanonical.isSemibounded_of_isPositive_shift` {Dom : Submodule ℂ F} (H : D →ₗ[ℂ] F) (c : ℝ) (A : Dom →ₗ[ℂ] F) (hA : IsPositiveSelfAdjointExtension (H + (c : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.isSemibounded_of_isPositive_shift` {Dom : Submodule ℂ F} (H : D →ₗ[ℂ] F) (c : ℝ) (A : Dom →ₗ[ℂ] F) (hA : IsPositiveSelfAdjointExtension (H + (c : ℂ) • D.subtype) A) : IsSemiboundedSelfAdjointExtension c H (A - (c : ℂ) • Dom.subtype)
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.isSemibounded_of_isPositive_shift`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.isSemibounded_of_isPositive_shift
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {D : Submodule ℂ F}

theorem BookProof.FriedrichsCanonical.isSemibounded_of_isPositive_shift {Dom : Submodule ℂ F} (H : D →ₗ[ℂ] F) (c : ℝ)
    (A : Dom →ₗ[ℂ] F)
    (hA : IsPositiveSelfAdjointExtension (H + (c : ℂ) • D.subtype) A) :
    IsSemiboundedSelfAdjointExtension c H (A - (c : ℂ) • Dom.subtype) := by sorry
