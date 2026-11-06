-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_stopped_positive_horizon_atom_zero_without_strategy
-- name    : AvramDividend.Classical.avram_bv_env3_original_stopped_positive_horizon_atom_zero_without_strategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:59:10.575176+00:00
-- url     : https://prove2.me/theorems/ae7d2d61-f421-4568-9df1-6d1ab1560733
-- title:
--   Original stopped clock excludes positive horizon singleton for arbitrary dividend functions
-- statement:
--   At strictly positive T with σ≤T, the original stopped paymentTimes excludes T; hence original discounted dividendMeasure cash at the singleton T vanishes for arbitrary D without strategy hypotheses.
-- source:
--   Fully Proved original stopped horizon atom zero d654b5a9-602b-452a-8db4-46cbb0fb9f64, whose accepted Lean source has unused hD; original paymentTimes and dividendMeasure. Avram, Palmowski and Pistorius (2007), Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_stopped_positive_horizon_atom_zero_without_strategy
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (hT : 0 < T) (hσ : σ ≤ (T : ℝ≥0∞)) (q : ℝ) :
    (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0 := by sorry
