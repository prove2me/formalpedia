-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_dom_le_formDomain
-- name    : BookProof.FriedrichsCanonical.dom_le_formDomain
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-17T00:37:13.910183+00:00
-- url     : https://prove2.me/theorems/a19a0f90-bf8f-4ef1-954a-fea9b5799640
-- title:
--   `BookProof.FriedrichsCanonical.dom_le_formDomain` (P : PosSymOp F) : P.dom ≤ formDomain P
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.dom_le_formDomain` (P : PosSymOp F) : P.dom ≤ formDomain P
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.dom_le_formDomain`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.dom_le_formDomain
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterQgOuterFockFarisLavine
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.QgOuterFockFL
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.FriedrichsCanonical.dom_le_formDomain (P : PosSymOp F) : P.dom ≤ formDomain P := by sorry
