-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_friedrichsOp_apply
-- name    : BookProof.FriedrichsCanonical.friedrichsOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:37:40.384016+00:00
-- url     : https://prove2.me/theorems/d298e859-832d-46c8-9c16-ea8dde0c410d
-- title:
--   `BookProof.FriedrichsCanonical.friedrichsOp_apply` (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) (y : friedrichsDomain P) : friedrichsOp P hdense y = preim (friedrichsResolvent
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.friedrichsOp_apply` (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) (y : friedrichsDomain P) : friedrichsOp P hdense y = preim (friedrichsResolvent P) y - ((1 : ℝ) : ℂ) • (y : F)
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.friedrichsOp_apply`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.friedrichsOp_apply
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHashimotoShiftInvert
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.FriedrichsCanonical.friedrichsOp_apply (P : PosSymOp F) (hdense : Dense (P.dom : Set F))
    (y : friedrichsDomain P) :
    friedrichsOp P hdense y
      = preim (friedrichsResolvent P) y - ((1 : ℝ) : ℂ) • (y : F) := by sorry
