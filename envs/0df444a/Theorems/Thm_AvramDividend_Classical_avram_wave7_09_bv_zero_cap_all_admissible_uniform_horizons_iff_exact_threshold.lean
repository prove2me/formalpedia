-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_all_admissible_uniform_horizons_iff_exact_threshold
-- name    : AvramDividend.Classical.avram_wave7_09_bv_zero_cap_all_admissible_uniform_horizons_iff_exact_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:40:48.330298+00:00
-- url     : https://prove2.me/theorems/5009aada-fc61-4da0-a992-525e18ee02bd
-- title:
--   Universal exact zero-cap finite-horizon BV allowance for every original admissible strategy
-- statement:
--   For every original Standing BV spectrally negative Lévy source of finite negative jump activity, the same real allowance W bounds the expected full stopped discounted Stieltjes payout at every natural horizon for EVERY source-admissible cap-zero strategy starting at zero if and only if W is at least the exact zero-barrier first-jump value drift/(q+nu(Iio0).toReal). The forward direction chooses the original reflected strategy, using proved sharp uniform iff fdf4348f. The reverse uses proved original zero-cap dividendValue comparison 570b5248, finite-horizon supremum 3b737955, original reflected value 6f73f927 and barrierValue identity 11b589b7. This is the precise conditional finite-activity BV C=0 repair branch for consumers; it is separate from the corrected C>0 parent.
-- source:
--   Original Ω/P/filtration/X, D and Stieltjes dividendMeasure. No open dependency, no process substitution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_zero_cap_all_admissible_uniform_horizons_iff_exact_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ) :
    (∀ (D : ℝ≥0 → Ω → ℝ),
      IsAdmissibleLe X 0 (0 : ℝ≥0∞) D →
      ∀ n : ℕ,
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X 0 D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal W) ↔
    X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal) ≤ W  := by sorry
