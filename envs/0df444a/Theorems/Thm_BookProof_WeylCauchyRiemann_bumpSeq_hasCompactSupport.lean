-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_bumpSeq_hasCompactSupport
-- name    : BookProof.WeylCauchyRiemann.bumpSeq_hasCompactSupport
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:14:55.637627+00:00
-- url     : https://prove2.me/theorems/1b0c15cd-2206-4e44-a085-b0a6ea8ea5ab
-- title:
--   `BookProof.WeylCauchyRiemann.bumpSeq_hasCompactSupport` (n : ℕ) : HasCompactSupport ((bumpSeq n).normed volume)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.bumpSeq_hasCompactSupport` (n : ℕ) : HasCompactSupport ((bumpSeq n).normed volume)
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.bumpSeq_hasCompactSupport`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.bumpSeq_hasCompactSupport
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.bumpSeq_hasCompactSupport (n : ℕ) :
    HasCompactSupport ((bumpSeq n).normed volume) := by sorry
