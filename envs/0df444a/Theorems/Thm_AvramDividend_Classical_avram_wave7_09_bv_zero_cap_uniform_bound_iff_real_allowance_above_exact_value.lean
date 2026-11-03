-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_uniform_bound_iff_real_allowance_above_exact_value
-- name    : AvramDividend.Classical.avram_wave7_09_bv_zero_cap_uniform_bound_iff_real_allowance_above_exact_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:19:08.464736+00:00
-- url     : https://prove2.me/theorems/fdf4348f-67d1-4999-bfa5-dee6c3b40749
-- title:
--   Exact necessary and sufficient uniform original BV zero-cap Stieltjes allowance threshold
-- statement:
--   For the same original Standing finite-jump-activity bounded-variation spectrally negative Lévy source at zero reserve and zero cap, and any real W and q>0, every finite natural-horizon expected full stopped discounted Stieltjes payout is at most ENNReal.ofReal W if and only if W is at least the sharp exact reflected value drift/(q+ν(Iio 0).toReal). Necessity is the previously Proved real threshold 3fa019a2. Sufficiency follows from each finite horizon being below the original dividendValue as an iSup and from the Proved exact first-jump value theorem, captured in the newly published all-horizon sufficiency helper. This fully characterises the zero-cap boundary case under the explicit finite-activity BV source hypothesis; it is separate from the corrected positive-cap stochastic parent and does not pretend that source exists unconditionally.
-- source:
--   Original source Ω/P/𝓕/X, cap-zero admissible barrierStrategy, ruinTime, paymentTimes and dividendMeasure. Direct imports only Proved 3fa019a2 and new Proved candidate for every horizon below reflected value.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_zero_cap_uniform_bound_iff_real_allowance_above_exact_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ) :
    (∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
      ENNReal.ofReal W) ↔
    X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal) ≤ W := by sorry
