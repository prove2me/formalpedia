-- Prove2me | Theorems.Thm_BookProof_FriedrichsFormGap_friedrichs_extension_form_gap
-- name    : BookProof.FriedrichsFormGap.friedrichs_extension_form_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:13:38.755307+00:00
-- url     : https://prove2.me/theorems/a6438d0d-8ea5-42f2-8363-8022b4afc0a2
-- title:
--   (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) {mu : ℝ} (hmu : ∀ x : P.dom, mu * ‖(x : F)‖ ^ 2 ≤ quadForm P.op x) : ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (S : F...
-- statement:
--   Lean 4 theorem `BookProof.FriedrichsFormGap.friedrichs_extension_form_gap` (module `BookProof.FriedrichsFormGap`), source chapter `BookProof/ChapterFriedrichsFormGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFriedrichsFormGap.lean

-- Generated from ChapterFriedrichsFormGap.lean — theorem BookProof.FriedrichsFormGap.friedrichs_extension_form_gap
import Mathlib
import Definitions.Def_ChapterFriedrichsFormGap
open BookProof.FriedrichsFormGap







noncomputable section


open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.FriedrichsFormGap.friedrichs_extension_form_gap (P : PosSymOp F) (hdense : Dense (P.dom : Set F))
    {mu : ℝ} (hmu : ∀ x : P.dom, mu * ‖(x : F)‖ ^ 2 ≤ quadForm P.op x) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (S : F →L[ℂ] F),
      IsPositiveSelfAdjointExtension P.op A ∧ IsShiftInvert A 1 S ∧
        IsSelfAdjoint S ∧ (∀ y : Dom, mu * ‖(y : F)‖ ^ 2 ≤ quadForm A y) := by sorry
