-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_ruined_oscillating_closed_crossing_cash_without_reference_grid
-- name    : AvramDividend.Classical.avram_bv_env3_original_ruined_oscillating_closed_crossing_cash_without_reference_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:46:04.033571+00:00
-- url     : https://prove2.me/theorems/f343d31d-89fb-423a-ba36-7f15ec52447a
-- title:
--   Ruined original payment clock makes the final closed crossing-cell cash vanish on an oscillating grid
-- statement:
--   For original paymentTimes σ stopped at or before a strictly positive horizon T and any potentially oscillating physical-grid endpoints a_n<T converging to T, the original closed discounted crossing-cell dividend cash on (a_n,T] tends to zero. There is no reference-grid requirement, and the proof retains the original ruin-payment strict support condition.
-- source:
--   Fully Proved original no-reference closed-cell limit and original stopped-clock horizon-atom-zero theorem d654b5a9-602b-452a-8db4-46cbb0fb9f64; Avram, Palmowski and Pistorius (2007), Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_ruined_oscillating_closed_crossing_cash_without_reference_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (hT : 0 < T) (hσ : σ ≤ (T : ℝ≥0∞))
    (q : ℝ) (hq : 0 ≤ q)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (nhds (T : ℝ)))
    (hbelow : ∀ n, a n < (T : ℝ)) :
    Tendsto (fun n =>
      ∫⁻ t in paymentTimes σ ∩ Ioc (a n) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by sorry
