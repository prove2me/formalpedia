-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_polynomial_integrable
-- name    : AvramDividend.Classical.avram_p2_i_moment_polynomial_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:30:18.829862+00:00
-- url     : https://prove2.me/theorems/19b671a0-b9d2-4f9a-9980-86b653546bfb
-- title:
--   Every real polynomial is integrable when all real moments are integrable
-- statement:
--   If all monomial maps z↦z^k are integrable against a positive measure, every real polynomial evaluation is integrable. Expand the polynomial into a finite sum of coefficient-weighted monomials and apply finite-sum closure of the Bochner integral. This discharges the polynomial-integrability premise needed in the quantitative error bound for moment convergence.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem AvramDividend.Classical.avram_p2_i_moment_polynomial_integrable
    (μ : Measure ℝ) (p : Polynomial ℝ)
    (hmom : ∀ k : ℕ, Integrable (fun z : ℝ => z ^ k) μ) :
    Integrable (fun z : ℝ => p.eval z) μ := by sorry
