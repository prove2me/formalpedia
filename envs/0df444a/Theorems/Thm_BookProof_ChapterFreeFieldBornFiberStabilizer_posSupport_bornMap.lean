-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberStabilizer_posSupport_bornMap
-- name    : BookProof.ChapterFreeFieldBornFiberStabilizer.posSupport_bornMap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:30:57.682759+00:00
-- url     : https://prove2.me/theorems/34e3b46c-eeb9-4382-a895-ae9e105a4759
-- title:
--   `BookProof.ChapterFreeFieldBornFiberStabilizer.posSupport_bornMap` (x : EuclideanSpace ℝ (Fin n)) : posSupport (bornMap x) = Finset.univ.filter (fun k => x k ≠ 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberStabilizer`.
--
--   `BookProof.ChapterFreeFieldBornFiberStabilizer.posSupport_bornMap` (x : EuclideanSpace ℝ (Fin n)) : posSupport (bornMap x) = Finset.univ.filter (fun k => x k ≠ 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberStabilizer.posSupport_bornMap`.

-- Generated from ChapterFreeFieldBornFiberStabilizer.lean — theorem BookProof.ChapterFreeFieldBornFiberStabilizer.posSupport_bornMap
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

theorem BookProof.ChapterFreeFieldBornFiberStabilizer.posSupport_bornMap (x : EuclideanSpace ℝ (Fin n)) :
    posSupport (bornMap x) = Finset.univ.filter (fun k => x k ≠ 0) := by sorry
