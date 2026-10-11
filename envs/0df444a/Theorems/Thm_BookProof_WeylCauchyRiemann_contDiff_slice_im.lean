-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_contDiff_slice_im
-- name    : BookProof.WeylCauchyRiemann.contDiff_slice_im
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:35:04.35399+00:00
-- url     : https://prove2.me/theorems/43c3f9b0-f01f-46d6-8027-c9ffde50ede3
-- title:
--   `BookProof.WeylCauchyRiemann.contDiff_slice_im` (x : ℝ) : ContDiff ℝ ∞ (fun t : ℝ => (x : ℂ) + t * Complex.I)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.contDiff_slice_im` (x : ℝ) : ContDiff ℝ ∞ (fun t : ℝ => (x : ℂ) + t * Complex.I)
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.contDiff_slice_im`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.contDiff_slice_im
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.contDiff_slice_im (x : ℝ) : ContDiff ℝ ∞ (fun t : ℝ => (x : ℂ) + t * Complex.I) := by sorry
