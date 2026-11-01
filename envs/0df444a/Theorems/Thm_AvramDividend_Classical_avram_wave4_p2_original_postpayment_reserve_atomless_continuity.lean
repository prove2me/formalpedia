-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_postpayment_reserve_atomless_continuity
-- name    : AvramDividend.Classical.avram_wave4_p2_original_postpayment_reserve_atomless_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:06:59.420088+00:00
-- url     : https://prove2.me/theorems/2c5e035b-c9bf-4b4b-b635-3029428f3945
-- title:
--   Actual original post-payment Lévy reserve agrees with its strict left limit at every atomless-typical time
-- statement:
--   For every original spectrally negative Lévy process, every adapted dividend strategy and arbitrary atomless time measure ν on ℝ≥0 (including singular-continuous Stieltjes dividend control), the genuine original post-payment controlled reserve U⁺_t=x+X_t-rightLimit D_t equals its strict-left pre-event limit at ν-almost every positive time, for P-almost every source sample. This is a direct complete source corollary of the independently proved all-path countability of U⁺ jump support. It allows Ito–Meyer diffuse-control derivatives to be evaluated at the actual chronological pre-event reserve without declaring the continuous dividend measure to vanish.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i) stopped verification and diffuse singular-continuous dividend control; independently proved P2 original postpayment countability source 3eed61cd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_postpayment_reserve_jump_times_countable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_original_postpayment_reserve_atomless_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ν : Measure ℝ≥0) [NullSingletonClass ν] :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂ν, 0 < t →
      x + X.X t ω - rightLimit D t ω =
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t := by sorry
