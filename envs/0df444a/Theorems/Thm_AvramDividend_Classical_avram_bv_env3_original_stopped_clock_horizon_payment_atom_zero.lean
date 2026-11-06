-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_stopped_clock_horizon_payment_atom_zero
-- name    : AvramDividend.Classical.avram_bv_env3_original_stopped_clock_horizon_payment_atom_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:18:18.100594+00:00
-- url     : https://prove2.me/theorems/d654b5a9-602b-452a-8db4-46cbb0fb9f64
-- title:
--   Original stopped payment clock excludes the positive horizon singleton at or after ruin
-- statement:
--   For a strictly positive real horizon T and any original payment clock stopped at or before T, the actual paymentTimes σ cannot contain T, because payments are permitted at time zero or strictly before σ. The discounted dividendMeasure mass at singleton T is therefore zero. This is the ruin-clock half of the final-cell atom analysis, and does not assert anything about surviving paths where σ>T.
-- source:
--   Original paymentTimes definition and dividendMeasure. Avram, Palmowski and Pistorius (2007), Proposition 4(i), equation (5.13). Complements Proved BV-ENV3 strict crossing cell and closed cash split, retaining horizon payments on surviving paths.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_stopped_clock_horizon_payment_atom_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (_hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (hT : 0 < T) (hσ : σ ≤ (T : ℝ≥0∞)) (q : ℝ) :
    (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0 := by sorry
