-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberStabilizer_boolSign_pm_inc
-- name    : BookProof.ChapterFreeFieldBornFiberStabilizer.boolSign_pm_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:14:40.567891+00:00
-- url     : https://prove2.me/theorems/e764f2bc-f924-462a-84cf-8c84e4f452c5
-- title:
--   `BookProof.ChapterFreeFieldBornFiberStabilizer.boolSign_pm_inc` (b : Fin n → Bool) (k : Fin n) : boolSign b k = 1 ∨ boolSign b k = -1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberStabilizer`.
--
--   `BookProof.ChapterFreeFieldBornFiberStabilizer.boolSign_pm_inc` (b : Fin n → Bool) (k : Fin n) : boolSign b k = 1 ∨ boolSign b k = -1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberStabilizer.boolSign_pm_inc`.
--
--   Replaces the unuploadable node `BookProof_ChapterFreeFieldBornFiberStabilizer_boolSign_pm`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterFreeFieldBornFiberStabilizer.lean — theorem BookProof.ChapterFreeFieldBornFiberStabilizer.boolSign_pm_inc
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornFiberBounds
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberStabilizer
open BookProof.ChapterFreeFieldBornFiberStabilizer


open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberBounds


variable {n : ℕ}

theorem BookProof.ChapterFreeFieldBornFiberStabilizer.boolSign_pm_inc (b : Fin n → Bool) (k : Fin n) :
    boolSign b k = 1 ∨ boolSign b k = -1 := by sorry
