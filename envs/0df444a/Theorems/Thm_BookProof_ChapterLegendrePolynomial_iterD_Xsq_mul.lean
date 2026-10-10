-- Prove2me | Theorems.Thm_BookProof_ChapterLegendrePolynomial_iterD_Xsq_mul
-- name    : BookProof.ChapterLegendrePolynomial.iterD_Xsq_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:27:08.869031+00:00
-- url     : https://prove2.me/theorems/af88774e-7647-4c11-aab0-0462b1c822dc
-- title:
--   `BookProof.ChapterLegendrePolynomial.iterD_Xsq_mul` (k : ℕ) (f : ℝ[X]) : derivative^[k] (X ^ 2 * f) = X ^ 2 * derivative^[k] f + C (2 * (k : ℝ)) * X * derivative^[k-1] f + C ((k :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLegendrePolynomial`.
--
--   `BookProof.ChapterLegendrePolynomial.iterD_Xsq_mul` (k : ℕ) (f : ℝ[X]) : derivative^[k] (X ^ 2 * f) = X ^ 2 * derivative^[k] f + C (2 * (k : ℝ)) * X * derivative^[k-1] f + C ((k : ℝ) * ((k : ℝ) - 1)) * derivative^[k-2] f
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLegendrePolynomial.iterD_Xsq_mul`.

-- Generated from ChapterLegendrePolynomial.lean — theorem BookProof.ChapterLegendrePolynomial.iterD_Xsq_mul
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterLegendrePolynomial



open Polynomial

theorem BookProof.ChapterLegendrePolynomial.iterD_Xsq_mul (k : ℕ) (f : ℝ[X]) :
    derivative^[k] (X ^ 2 * f)
      = X ^ 2 * derivative^[k] f + C (2 * (k : ℝ)) * X * derivative^[k-1] f
        + C ((k : ℝ) * ((k : ℝ) - 1)) * derivative^[k-2] f := by sorry
