-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_hasCompactSupport_fderiv_apply
-- name    : BookProof.WeylCauchyRiemann.hasCompactSupport_fderiv_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:34:52.311857+00:00
-- url     : https://prove2.me/theorems/13a972a7-6836-4fbf-963c-1f863b14e33c
-- title:
--   `BookProof.WeylCauchyRiemann.hasCompactSupport_fderiv_apply` {ψ : ℂ → ℂ} (hψc : HasCompactSupport ψ) (v : ℂ) : HasCompactSupport (fun z : ℂ => fderiv ℝ ψ z v)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.hasCompactSupport_fderiv_apply` {ψ : ℂ → ℂ} (hψc : HasCompactSupport ψ) (v : ℂ) : HasCompactSupport (fun z : ℂ => fderiv ℝ ψ z v)
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.hasCompactSupport_fderiv_apply`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.hasCompactSupport_fderiv_apply
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.hasCompactSupport_fderiv_apply {ψ : ℂ → ℂ} (hψc : HasCompactSupport ψ) (v : ℂ) :
    HasCompactSupport (fun z : ℂ => fderiv ℝ ψ z v) := by sorry
