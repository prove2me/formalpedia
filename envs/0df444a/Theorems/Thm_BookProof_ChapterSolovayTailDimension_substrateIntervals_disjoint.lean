-- Prove2me | Theorems.Thm_BookProof_ChapterSolovayTailDimension_substrateIntervals_disjoint
-- name    : BookProof.ChapterSolovayTailDimension.substrateIntervals_disjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T12:22:16.470995+00:00
-- url     : https://prove2.me/theorems/ce6a273d-bd64-4bb3-955b-55039cb574af
-- title:
--   `BookProof.ChapterSolovayTailDimension.substrateIntervals_disjoint` {m n : ℕ} (h : m ≠ n) : substrateInterval m ∩ substrateInterval n = ∅
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovayTailDimension`.
--
--   `BookProof.ChapterSolovayTailDimension.substrateIntervals_disjoint` {m n : ℕ} (h : m ≠ n) : substrateInterval m ∩ substrateInterval n = ∅
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovayTailDimension.substrateIntervals_disjoint`.

-- Generated from ChapterSolovayTailDimension.lean — theorem BookProof.ChapterSolovayTailDimension.substrateIntervals_disjoint
import Mathlib
import Definitions.Def_ChapterSolovayTailDimension
open BookProof.ChapterSolovayTailDimension


noncomputable section

open MeasureTheory Set PhysMehler PhysMeasureBasis
open scoped ENNReal

theorem BookProof.ChapterSolovayTailDimension.substrateIntervals_disjoint {m n : ℕ} (h : m ≠ n) :
    substrateInterval m ∩ substrateInterval n = ∅ := by sorry
