-- Prove2me | Theorems.Thm_BookProof_FriedrichsFormGap_friedrichs_quadForm_lower_bound
-- name    : BookProof.FriedrichsFormGap.friedrichs_quadForm_lower_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T08:00:12.334989+00:00
-- url     : https://prove2.me/theorems/ea16147e-8dce-40d7-a0fd-f2bf9ef18f66
-- title:
--   (P : PosSymOp F) (hinj : Function.Injective (friedrichsResolvent P)) {mu : ℝ} (hmu : ∀ x : P.dom, mu * ‖(x : F)‖ ^ 2 ≤ quadForm P.op x) (y : LinearMap.range ((friedrichsResolvent P) :...
-- statement:
--   Lean 4 theorem `BookProof.FriedrichsFormGap.friedrichs_quadForm_lower_bound` (module `BookProof.FriedrichsFormGap`), source chapter `BookProof/ChapterFriedrichsFormGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFriedrichsFormGap.lean

-- Generated from ChapterFriedrichsFormGap.lean — theorem BookProof.FriedrichsFormGap.friedrichs_quadForm_lower_bound
import Mathlib
import Definitions.Def_ChapterFriedrichsFormGap
open BookProof.FriedrichsFormGap







noncomputable section


open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.FriedrichsFormGap.friedrichs_quadForm_lower_bound (P : PosSymOp F)
    (hinj : Function.Injective (friedrichsResolvent P)) {mu : ℝ}
    (hmu : ∀ x : P.dom, mu * ‖(x : F)‖ ^ 2 ≤ quadForm P.op x)
    (y : LinearMap.range ((friedrichsResolvent P) : F →ₗ[ℂ] F)) :
    mu * ‖(y : F)‖ ^ 2 ≤ quadForm (invShiftOperator (friedrichsResolvent P) hinj 1) y := by sorry
