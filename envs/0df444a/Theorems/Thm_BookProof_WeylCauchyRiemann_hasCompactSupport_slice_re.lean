-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_hasCompactSupport_slice_re
-- name    : BookProof.WeylCauchyRiemann.hasCompactSupport_slice_re
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:33:43.709985+00:00
-- url     : https://prove2.me/theorems/b75eee30-4f45-4b88-9874-d291e392468c
-- title:
--   `BookProof.WeylCauchyRiemann.hasCompactSupport_slice_re` {ψ : ℂ → ℂ} (hψc : HasCompactSupport ψ) (y : ℝ) : HasCompactSupport (fun t : ℝ => ψ ((t : ℂ) + y * Complex.I))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.hasCompactSupport_slice_re` {ψ : ℂ → ℂ} (hψc : HasCompactSupport ψ) (y : ℝ) : HasCompactSupport (fun t : ℝ => ψ ((t : ℂ) + y * Complex.I))
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.hasCompactSupport_slice_re`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.hasCompactSupport_slice_re
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.hasCompactSupport_slice_re {ψ : ℂ → ℂ} (hψc : HasCompactSupport ψ) (y : ℝ) :
    HasCompactSupport (fun t : ℝ => ψ ((t : ℂ) + y * Complex.I)) := by sorry
