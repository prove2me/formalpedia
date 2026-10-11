-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_mollify_moll_eq_self
-- name    : BookProof.WeylCauchyRiemann.mollify_moll_eq_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:14:45.019012+00:00
-- url     : https://prove2.me/theorems/1bc624e4-d4e7-48ff-92ec-9e04c940f91a
-- title:
--   `BookProof.WeylCauchyRiemann.mollify_moll_eq_self` {h : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hh : DifferentiableOn ℂ h s) (hcont : Continuous h) {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.mollify_moll_eq_self` {h : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hh : DifferentiableOn ℂ h s) (hcont : Continuous h) {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : closedBall z δ ⊆ s) : mollify h (moll δ) z = h z
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.mollify_moll_eq_self`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.mollify_moll_eq_self
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.mollify_moll_eq_self {h : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s)
    (hh : DifferentiableOn ℂ h s) (hcont : Continuous h) {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : closedBall z δ ⊆ s) : mollify h (moll δ) z = h z := by sorry
