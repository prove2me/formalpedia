-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_friedrichsOp_isPositiveSelfAdjointExtension
-- name    : BookProof.FriedrichsCanonical.friedrichsOp_isPositiveSelfAdjointExtension
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-17T00:37:46.691304+00:00
-- url     : https://prove2.me/theorems/5b7567f8-d5ef-4a32-93a7-98b12249a9ea
-- title:
--   `BookProof.FriedrichsCanonical.friedrichsOp_isPositiveSelfAdjointExtension` (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) : IsPositiveSelfAdjointExtension P.op (friedrichsOp P
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.friedrichsOp_isPositiveSelfAdjointExtension` (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) : IsPositiveSelfAdjointExtension P.op (friedrichsOp P hdense)
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.friedrichsOp_isPositiveSelfAdjointExtension`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.friedrichsOp_isPositiveSelfAdjointExtension
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.QgOuterFockFL
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.FriedrichsCanonical.friedrichsOp_isPositiveSelfAdjointExtension (P : PosSymOp F)
    (hdense : Dense (P.dom : Set F)) :
    IsPositiveSelfAdjointExtension P.op (friedrichsOp P hdense) := by sorry
