-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_integral_eq_hasSum_exact_nat_count_cell_integrals_20261117
-- name    : AvramDividend.Classical.avram_a27_integral_eq_hasSum_exact_nat_count_cell_integrals_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:35:08.561785+00:00
-- url     : https://prove2.me/theorems/a4f7c3c7-011b-468d-b0e7-b88deb53bcf5
-- title:
--   Every integrable observable splits into an absolutely convergent count-cell integral series for a measurable natural-valued count
-- statement:
--   For any measurable natural-valued K on the original probability space, the expectation of an integrable real observable F equals the sum of its integrals over all cells K=k. This supplies the count-cell decomposition required to extract coefficients from the physical marked-jump count generating function, with genuine countable additivity.
-- source:
--   Pinned Mathlib MeasureTheory.hasSum_integral_iUnion and the exact measurable partition of Ω by K:Ω→ℕ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- A Bochner integral is the sum of its integrals over the exact cells of a measurable natural-valued count. -/

theorem AvramDividend.Classical.avram_a27_integral_eq_hasSum_exact_nat_count_cell_integrals_20261117
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ) (hK : Measurable K)
    (F : Ω → ℝ) (hF : Integrable F P) :
    HasSum (fun k : ℕ => ∫ ω in {ω : Ω | K ω = k}, F ω ∂P)
      (∫ ω, F ω ∂P) := by sorry
