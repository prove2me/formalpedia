-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_actual_right_payment_jumps_summable_on_atom_support
-- name    : AvramDividend.Classical.avram_wave4_04b_finite_horizon_actual_right_payment_jumps_summable_on_atom_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:59:18.099131+00:00
-- url     : https://prove2.me/theorems/884b54aa-9e94-4d3c-b64b-f4d8f074fd91
-- title:
--   Finite Stieltjes singleton-mass convergence equals summability of genuine chronological dividend right-payment increments
-- statement:
--   On the original adapted monotone dividend strategy, for any real atom support inside [0,T], the exact dividend Stieltjes singleton mass equals the nonnegative chronological right dividend jump D_t^+−D_t. Consequently, summability of actual finite-horizon real singleton masses implies summability of those actual chronological increments. Time zero and the terminal time are retained. No pure-atomic assumption is imposed, and singular-continuous dividend mass remains outside this atom summation.
-- source:
--   Canonically Proved source dividendMeasure_singleton_eq_rightLimit_sub and dividendStrategy_le_rightLimit; Mathlib ENNReal.toReal_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_finite_horizon_actual_right_payment_jumps_summable_on_atom_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (A : Set ℝ)
    (hAwindow : ∀ s : A, (0 : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) ≤ (T : ℝ))
    (hMass : Summable (fun s : A => (((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) {(s : ℝ)}).toReal)) :
    Summable (fun s : A => rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) := by sorry
