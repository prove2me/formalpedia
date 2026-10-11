-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_bumpSeq_contDiff
-- name    : BookProof.WeylCauchyRiemann.bumpSeq_contDiff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:14:52.6956+00:00
-- url     : https://prove2.me/theorems/c3adb3dd-8f7f-4562-84f4-200f20d34af3
-- title:
--   `BookProof.WeylCauchyRiemann.bumpSeq_contDiff` (n : ℕ) : ContDiff ℝ ∞ ((bumpSeq n).normed volume)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.bumpSeq_contDiff` (n : ℕ) : ContDiff ℝ ∞ ((bumpSeq n).normed volume)
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.bumpSeq_contDiff`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.bumpSeq_contDiff
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.bumpSeq_contDiff (n : ℕ) : ContDiff ℝ ∞ ((bumpSeq n).normed volume) := by sorry
