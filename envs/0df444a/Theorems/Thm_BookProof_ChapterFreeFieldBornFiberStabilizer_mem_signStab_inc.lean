-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberStabilizer_mem_signStab_inc
-- name    : BookProof.ChapterFreeFieldBornFiberStabilizer.mem_signStab_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:15:00.939122+00:00
-- url     : https://prove2.me/theorems/b3f42d8a-094f-490e-835e-a3dd907d9730
-- title:
--   `BookProof.ChapterFreeFieldBornFiberStabilizer.mem_signStab_inc` {x : EuclideanSpace ℝ (Fin n)} {b : Fin n → Bool} : b ∈ signStab x ↔ ∀ k, x k ≠ 0 → b k = true
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberStabilizer`.
--
--   `BookProof.ChapterFreeFieldBornFiberStabilizer.mem_signStab_inc` {x : EuclideanSpace ℝ (Fin n)} {b : Fin n → Bool} : b ∈ signStab x ↔ ∀ k, x k ≠ 0 → b k = true
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberStabilizer.mem_signStab_inc`.
--
--   Replaces the unuploadable node `BookProof_ChapterFreeFieldBornFiberStabilizer_mem_signStab`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterFreeFieldBornFiberStabilizer.lean — theorem BookProof.ChapterFreeFieldBornFiberStabilizer.mem_signStab_inc
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

theorem BookProof.ChapterFreeFieldBornFiberStabilizer.mem_signStab_inc {x : EuclideanSpace ℝ (Fin n)} {b : Fin n → Bool} :
    b ∈ signStab x ↔ ∀ k, x k ≠ 0 → b k = true := by sorry
