-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_integral_complex_eq_prod
-- name    : BookProof.WeylCauchyRiemann.integral_complex_eq_prod
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:33:50.420275+00:00
-- url     : https://prove2.me/theorems/d65a14a5-2202-4996-bdee-40f8ff5c5d29
-- title:
--   `BookProof.WeylCauchyRiemann.integral_complex_eq_prod` (G : ℂ → ℂ) : ∫ z : ℂ, G z = ∫ p : ℝ × ℝ, G (p.1 + p.2 * Complex.I)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.integral_complex_eq_prod` (G : ℂ → ℂ) : ∫ z : ℂ, G z = ∫ p : ℝ × ℝ, G (p.1 + p.2 * Complex.I)
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.integral_complex_eq_prod`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.integral_complex_eq_prod
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.integral_complex_eq_prod (G : ℂ → ℂ) :
    ∫ z : ℂ, G z = ∫ p : ℝ × ℝ, G (p.1 + p.2 * Complex.I) := by sorry
