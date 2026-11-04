-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_exact_discount_cell_finite_of_mass_finite
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_exact_discount_cell_finite_of_mass_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:02:36.417216+00:00
-- url     : https://prove2.me/theorems/42e5bd52-74b5-410d-ab5d-c91771fec6ed
-- title:
--   Finite original dividend Stieltjes cell mass gives finite literal discounted cash
-- statement:
--   On any original dividend Stieltjes cell (a,b] with finite source measure mass, the exact exponentially discounted ENNReal payment-time lintegral is finite. The discount is at most one on nonnegative times, and the proved source exact cell sandwich bounds the whole integral by the undiscounted cell mass. This rules out hidden infinity-to-zero conversion when passing to real-valued Cash, conditional on finite cell mass.
-- source:
--   Proved source full Stieltjes exact-discount cell endpoint sandwich and Real.exp_le_one_iff; original dividendMeasure cash

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_exact_discount_cell_endpoint_sandwich

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_exact_discount_cell_finite_of_mass_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ≥0)
    (hmass : dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) < ⊤) :
    (∫⁻ u in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) < ⊤ := by sorry
