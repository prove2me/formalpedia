-- Prove2me | Theorems.Thm_BookProof_ChapterLegendrePolynomial_rec_coeff_ne_zero
-- name    : BookProof.ChapterLegendrePolynomial.rec_coeff_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:29:05.009689+00:00
-- url     : https://prove2.me/theorems/251f006f-8458-4356-9af7-141b12cfd360
-- title:
--   `BookProof.ChapterLegendrePolynomial.rec_coeff_ne_zero` (l μ j : ℕ) (h : μ ≤ l) (hne : j ≠ l - μ) : ((j : ℝ) * ((j : ℝ) - 1) + (2 * (μ : ℝ) + 2) * j + ((μ : ℝ) * ((μ : ℝ) +...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLegendrePolynomial`.
--
--   `BookProof.ChapterLegendrePolynomial.rec_coeff_ne_zero` (l μ j : ℕ) (h : μ ≤ l) (hne : j ≠ l - μ) : ((j : ℝ) * ((j : ℝ) - 1) + (2 * (μ : ℝ) + 2) * j + ((μ : ℝ) * ((μ : ℝ) + 1) - (l : ℝ) * ((l : ℝ) + 1))) ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLegendrePolynomial.rec_coeff_ne_zero`.

-- Generated from ChapterLegendrePolynomial.lean — theorem BookProof.ChapterLegendrePolynomial.rec_coeff_ne_zero
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterLegendrePolynomial



open Polynomial

theorem BookProof.ChapterLegendrePolynomial.rec_coeff_ne_zero (l μ j : ℕ) (h : μ ≤ l) (hne : j ≠ l - μ) :
    ((j : ℝ) * ((j : ℝ) - 1) + (2 * (μ : ℝ) + 2) * j
      + ((μ : ℝ) * ((μ : ℝ) + 1) - (l : ℝ) * ((l : ℝ) + 1))) ≠ 0 := by sorry
