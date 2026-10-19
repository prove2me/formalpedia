-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_resolvent_mem_friedrichsDomain
-- name    : BookProof.FriedrichsCanonical.resolvent_mem_friedrichsDomain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:37:20.092447+00:00
-- url     : https://prove2.me/theorems/6ab5fbd8-d136-45f4-8684-c1b58d5e8b61
-- title:
--   `BookProof.FriedrichsCanonical.resolvent_mem_friedrichsDomain` (P : PosSymOp F) (u : F) : friedrichsResolvent P u ∈ friedrichsDomain P
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.resolvent_mem_friedrichsDomain` (P : PosSymOp F) (u : F) : friedrichsResolvent P u ∈ friedrichsDomain P
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.resolvent_mem_friedrichsDomain`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.resolvent_mem_friedrichsDomain
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

theorem BookProof.FriedrichsCanonical.resolvent_mem_friedrichsDomain (P : PosSymOp F) (u : F) :
    friedrichsResolvent P u ∈ friedrichsDomain P := by sorry
