-- Prove2me | Theorems.Thm_BookProof_ChapterSirkSpectralGeometry_realSegment_subset_closedBall
-- name    : BookProof.ChapterSirkSpectralGeometry.realSegment_subset_closedBall
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:34:28.968692+00:00
-- url     : https://prove2.me/theorems/8008cc7a-21a7-4851-8fc9-aa7a143cd78c
-- title:
--   {a b : ℝ} (ha : 0 ≤ a) : realSegment a b ⊆ Metric.closedBall (0 : ℂ) b
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkSpectralGeometry.realSegment_subset_closedBall` (module `BookProof.ChapterSirkSpectralGeometry`), source chapter `BookProof/ChapterChapterSirkSpectralGeometry.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkSpectralGeometry.lean

-- Generated from ChapterSirkSpectralGeometry.lean — theorem BookProof.ChapterSirkSpectralGeometry.realSegment_subset_closedBall
import Mathlib
import Definitions.Def_ChapterSirkSpectralGeometry
open BookProof.ChapterSirkSpectralGeometry








noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.HashimotoShiftInvert BookProof.FarisLavine

theorem BookProof.ChapterSirkSpectralGeometry.realSegment_subset_closedBall {a b : ℝ} (ha : 0 ≤ a) :
    realSegment a b ⊆ Metric.closedBall (0 : ℂ) b := by sorry
