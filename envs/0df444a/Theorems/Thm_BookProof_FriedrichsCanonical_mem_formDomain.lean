-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_mem_formDomain
-- name    : BookProof.FriedrichsCanonical.mem_formDomain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:37:00.504818+00:00
-- url     : https://prove2.me/theorems/72828524-8815-48ac-aed9-282e0f68cfd0
-- title:
--   `BookProof.FriedrichsCanonical.mem_formDomain` {P : PosSymOp F} {v : F} (k : FormSpace P) (hk : formExt P k = v) : v ∈ formDomain P
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.mem_formDomain` {P : PosSymOp F} {v : F} (k : FormSpace P) (hk : formExt P k = v) : v ∈ formDomain P
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.mem_formDomain`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.mem_formDomain
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

theorem BookProof.FriedrichsCanonical.mem_formDomain {P : PosSymOp F} {v : F} (k : FormSpace P) (hk : formExt P k = v) :
    v ∈ formDomain P := by sorry
