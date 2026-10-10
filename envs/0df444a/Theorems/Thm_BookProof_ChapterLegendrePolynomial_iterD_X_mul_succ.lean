-- Prove2me | Theorems.Thm_BookProof_ChapterLegendrePolynomial_iterD_X_mul_succ
-- name    : BookProof.ChapterLegendrePolynomial.iterD_X_mul_succ
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:27:09.556271+00:00
-- url     : https://prove2.me/theorems/41301033-8e0c-486f-bb2a-6cd0fac8e3ff
-- title:
--   `BookProof.ChapterLegendrePolynomial.iterD_X_mul_succ` (k : ℕ) (f : ℝ[X]) : derivative^[k+1] (X * f) = X * derivative^[k+1] f + C ((k : ℝ) + 1) * derivative^[k] f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLegendrePolynomial`.
--
--   `BookProof.ChapterLegendrePolynomial.iterD_X_mul_succ` (k : ℕ) (f : ℝ[X]) : derivative^[k+1] (X * f) = X * derivative^[k+1] f + C ((k : ℝ) + 1) * derivative^[k] f
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLegendrePolynomial.iterD_X_mul_succ`.

-- Generated from ChapterLegendrePolynomial.lean — theorem BookProof.ChapterLegendrePolynomial.iterD_X_mul_succ
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterLegendrePolynomial



open Polynomial

theorem BookProof.ChapterLegendrePolynomial.iterD_X_mul_succ (k : ℕ) (f : ℝ[X]) :
    derivative^[k+1] (X * f) = X * derivative^[k+1] f + C ((k : ℝ) + 1) * derivative^[k] f := by sorry
