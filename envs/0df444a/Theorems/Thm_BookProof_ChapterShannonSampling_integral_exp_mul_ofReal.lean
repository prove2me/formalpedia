-- Prove2me | Theorems.Thm_BookProof_ChapterShannonSampling_integral_exp_mul_ofReal
-- name    : BookProof.ChapterShannonSampling.integral_exp_mul_ofReal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:23:20.113994+00:00
-- url     : https://prove2.me/theorems/8d2a964a-934a-4f30-af19-9bb8e5d0fb5b
-- title:
--   `BookProof.ChapterShannonSampling.integral_exp_mul_ofReal` (T a : ℝ) (hT : 0 < T) : (∫ ξ in (-(T / 2))..(T / 2), Complex.exp (2 * π * I * a * ξ)) = (T : ℂ) * (sinc (a * T) : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShannonSampling`.
--
--   `BookProof.ChapterShannonSampling.integral_exp_mul_ofReal` (T a : ℝ) (hT : 0 < T) : (∫ ξ in (-(T / 2))..(T / 2), Complex.exp (2 * π * I * a * ξ)) = (T : ℂ) * (sinc (a * T) : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterShannonSampling.integral_exp_mul_ofReal`.

-- Generated from ChapterShannonSampling.lean — theorem BookProof.ChapterShannonSampling.integral_exp_mul_ofReal
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling



open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

theorem BookProof.ChapterShannonSampling.integral_exp_mul_ofReal (T a : ℝ) (hT : 0 < T) :
    (∫ ξ in (-(T / 2))..(T / 2), Complex.exp (2 * π * I * a * ξ))
      = (T : ℂ) * (sinc (a * T) : ℝ) := by sorry
