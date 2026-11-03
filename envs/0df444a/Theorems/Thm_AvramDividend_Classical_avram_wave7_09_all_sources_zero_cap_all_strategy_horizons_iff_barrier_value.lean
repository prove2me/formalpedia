-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_all_sources_zero_cap_all_strategy_horizons_iff_barrier_value
-- name    : AvramDividend.Classical.avram_wave7_09_all_sources_zero_cap_all_strategy_horizons_iff_barrier_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:53:40.511553+00:00
-- url     : https://prove2.me/theorems/3bdd20be-954a-4a1c-9caa-546a6dfa4315
-- title:
--   All sources: exact zero-cap all-strategy natural-horizon Stieltjes budget iff actual barrier dividendValue
-- statement:
--   For any actual Standing spectrally negative Lévy source and q>0, the uniform original expected full stopped Stieltjes cash bound A for every cap-zero admissible D and every natural finite horizon holds exactly when the full original dividendValue of barrierStrategy X 0 0 is at most A. Necessity uses the original barrier's Proved admissibility 32b4ccb8 and Proved uniform natural-horizon-to-dividendValue bridge dc933bd8. Sufficiency combines the Proved original horizon iSup identity 3b737955 with the Proved all-source zero-cap strategy value domination 570b5248. This sharp boundary is valid with arbitrary jump activity and either bounded or unbounded variation; an explicit ratio is only claimed when the extra finite-activity BV hypotheses are supplied.
-- source:
--   Original Ω/P/filtration/X, paymentTimes, ruinTime, dividendMeasure and dividendValue; all imports Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_all_sources_zero_cap_all_strategy_horizons_iff_barrier_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (A : ℝ≥0∞) :
    (∀ (D : ℝ≥0 → Ω → ℝ),
      IsAdmissibleLe X 0 (0 : ℝ≥0∞) D →
      ∀ n : ℕ,
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X 0 D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ A) ↔
    dividendValue X q 0 (barrierStrategy X 0 0) ≤ A  := by sorry
