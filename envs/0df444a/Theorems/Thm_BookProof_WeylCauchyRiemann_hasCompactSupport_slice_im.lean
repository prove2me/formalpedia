-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_hasCompactSupport_slice_im
-- name    : BookProof.WeylCauchyRiemann.hasCompactSupport_slice_im
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:33:29.022211+00:00
-- url     : https://prove2.me/theorems/aefff194-2389-4b1d-82ba-ca7c64014adc
-- title:
--   `BookProof.WeylCauchyRiemann.hasCompactSupport_slice_im` {ψ : ℂ → ℂ} (hψc : HasCompactSupport ψ) (x : ℝ) : HasCompactSupport (fun t : ℝ => ψ ((x : ℂ) + t * Complex.I))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.hasCompactSupport_slice_im` {ψ : ℂ → ℂ} (hψc : HasCompactSupport ψ) (x : ℝ) : HasCompactSupport (fun t : ℝ => ψ ((x : ℂ) + t * Complex.I))
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.hasCompactSupport_slice_im`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.hasCompactSupport_slice_im
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.hasCompactSupport_slice_im {ψ : ℂ → ℂ} (hψc : HasCompactSupport ψ) (x : ℝ) :
    HasCompactSupport (fun t : ℝ => ψ ((x : ℂ) + t * Complex.I)) := by sorry
