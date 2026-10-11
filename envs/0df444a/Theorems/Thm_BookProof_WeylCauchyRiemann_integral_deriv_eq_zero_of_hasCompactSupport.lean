-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_integral_deriv_eq_zero_of_hasCompactSupport
-- name    : BookProof.WeylCauchyRiemann.integral_deriv_eq_zero_of_hasCompactSupport
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:33:13.966256+00:00
-- url     : https://prove2.me/theorems/49687a96-989e-435b-af5a-8e8ebf56fec2
-- title:
--   `BookProof.WeylCauchyRiemann.integral_deriv_eq_zero_of_hasCompactSupport` {u : ℝ → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) : ∫ t : ℝ, deriv u t = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.integral_deriv_eq_zero_of_hasCompactSupport` {u : ℝ → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) : ∫ t : ℝ, deriv u t = 0
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.integral_deriv_eq_zero_of_hasCompactSupport`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.integral_deriv_eq_zero_of_hasCompactSupport
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.integral_deriv_eq_zero_of_hasCompactSupport {u : ℝ → ℂ} (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) : ∫ t : ℝ, deriv u t = 0 := by sorry
