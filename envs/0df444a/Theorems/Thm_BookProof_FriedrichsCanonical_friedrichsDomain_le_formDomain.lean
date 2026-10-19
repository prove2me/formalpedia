-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_friedrichsDomain_le_formDomain
-- name    : BookProof.FriedrichsCanonical.friedrichsDomain_le_formDomain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:37:28.10341+00:00
-- url     : https://prove2.me/theorems/fb1a6d90-0b7c-403a-878a-6d4fc58db6ca
-- title:
--   `BookProof.FriedrichsCanonical.friedrichsDomain_le_formDomain` (P : PosSymOp F) : friedrichsDomain P ≤ formDomain P
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.friedrichsDomain_le_formDomain` (P : PosSymOp F) : friedrichsDomain P ≤ formDomain P
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.friedrichsDomain_le_formDomain`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.friedrichsDomain_le_formDomain
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.FriedrichsCanonical.friedrichsDomain_le_formDomain (P : PosSymOp F) :
    friedrichsDomain P ≤ formDomain P := by sorry
