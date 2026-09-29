-- Prove2me | Theorems.Thm_BookProof_FriedrichsFormGap_formSpace_norm_bound
-- name    : BookProof.FriedrichsFormGap.formSpace_norm_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:27:30.109394+00:00
-- url     : https://prove2.me/theorems/ed96c037-9d30-4390-8ea3-e53eadcbc944
-- title:
--   (P : PosSymOp F) {mu : ℝ} (hmu : ∀ x : P.dom, mu * ‖(x : F)‖ ^ 2 ≤ quadForm P.op x) (k : FormSpace P) : (1 + mu) * ‖formExt P k‖ ^ 2 ≤ ‖k‖ ^ 2
-- statement:
--   Lean 4 theorem `BookProof.FriedrichsFormGap.formSpace_norm_bound` (module `BookProof.FriedrichsFormGap`), source chapter `BookProof/ChapterFriedrichsFormGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFriedrichsFormGap.lean

-- Generated from ChapterFriedrichsFormGap.lean — theorem BookProof.FriedrichsFormGap.formSpace_norm_bound
import Mathlib
import Definitions.Def_ChapterFriedrichsFormGap
open BookProof.FriedrichsFormGap







noncomputable section


open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.FriedrichsFormGap.formSpace_norm_bound (P : PosSymOp F) {mu : ℝ}
    (hmu : ∀ x : P.dom, mu * ‖(x : F)‖ ^ 2 ≤ quadForm P.op x) (k : FormSpace P) :
    (1 + mu) * ‖formExt P k‖ ^ 2 ≤ ‖k‖ ^ 2 := by sorry
