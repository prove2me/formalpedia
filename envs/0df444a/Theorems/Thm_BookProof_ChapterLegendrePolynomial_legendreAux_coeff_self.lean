-- Prove2me | Theorems.Thm_BookProof_ChapterLegendrePolynomial_legendreAux_coeff_self
-- name    : BookProof.ChapterLegendrePolynomial.legendreAux_coeff_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:29:40.558612+00:00
-- url     : https://prove2.me/theorems/929b1096-b6f7-4ca4-b506-028fbe6be4eb
-- title:
--   `BookProof.ChapterLegendrePolynomial.legendreAux_coeff_self` (l : ℕ) : (legendreAux l).coeff l = ((2 * l).descFactorial l : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLegendrePolynomial`.
--
--   `BookProof.ChapterLegendrePolynomial.legendreAux_coeff_self` (l : ℕ) : (legendreAux l).coeff l = ((2 * l).descFactorial l : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLegendrePolynomial.legendreAux_coeff_self`.

-- Generated from ChapterLegendrePolynomial.lean — theorem BookProof.ChapterLegendrePolynomial.legendreAux_coeff_self
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterLegendrePolynomial



open Polynomial

theorem BookProof.ChapterLegendrePolynomial.legendreAux_coeff_self (l : ℕ) :
    (legendreAux l).coeff l = ((2 * l).descFactorial l : ℝ) := by sorry
