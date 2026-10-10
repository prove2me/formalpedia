-- Prove2me | Theorems.Thm_BookProof_ChapterLegendrePolynomial_iterD_X_mul
-- name    : BookProof.ChapterLegendrePolynomial.iterD_X_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:27:12.399334+00:00
-- url     : https://prove2.me/theorems/1b824bb9-e2e0-4654-a6dc-df154a42601e
-- title:
--   `BookProof.ChapterLegendrePolynomial.iterD_X_mul` (k : ℕ) (f : ℝ[X]) : derivative^[k] (X * f) = X * derivative^[k] f + C (k : ℝ) * derivative^[k-1] f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLegendrePolynomial`.
--
--   `BookProof.ChapterLegendrePolynomial.iterD_X_mul` (k : ℕ) (f : ℝ[X]) : derivative^[k] (X * f) = X * derivative^[k] f + C (k : ℝ) * derivative^[k-1] f
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLegendrePolynomial.iterD_X_mul`.

-- Generated from ChapterLegendrePolynomial.lean — theorem BookProof.ChapterLegendrePolynomial.iterD_X_mul
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterLegendrePolynomial



open Polynomial

theorem BookProof.ChapterLegendrePolynomial.iterD_X_mul (k : ℕ) (f : ℝ[X]) :
    derivative^[k] (X * f) = X * derivative^[k] f + C (k : ℝ) * derivative^[k-1] f := by sorry
