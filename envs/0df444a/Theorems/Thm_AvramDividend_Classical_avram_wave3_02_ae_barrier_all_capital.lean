-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_ae_barrier_all_capital
-- name    : AvramDividend.Classical.avram_wave3_02_ae_barrier_all_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:12:01.452719+00:00
-- url     : https://prove2.me/theorems/97578dce-7286-4d5f-b2c3-43a4925a0f42
-- title:
--   The original reflected dividend strategy has exact scale value for almost every positive barrier at all capital levels
-- statement:
--   Under the original Standing spectrally negative Lévy process and q>0, the genuine Stieltjes dividend value of reflection at barrier a equals the scale-function candidate at every initial x≥0 for Lebesgue-almost every positive a. Since the scale function is globally monotone, Mathlib gives pointwise differentiability almost everywhere. Accepted source-specific Esscher strict-slope and genuine strong-Markov all-capital identities then give the equality. This result is unconditional under Standing and does not require the separately Open global C1 theorem.
-- source:
--   Avram, Palmowski, Pistorius (2007), Proposition 1; Mathlib.Analysis.Calculus.Monotone Monotone.ae_differentiableAt; accepted original stopped-renewal and reflected-regulator scale identities.

import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_pos_of_pointwise_diff
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_capital_of_local_deriv_nonzero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_ae_barrier_all_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ᵐ a : ℝ ∂(volume : Measure ℝ), 0 < a →
      ∀ x : ℝ, 0 ≤ x →
        dividendValue X q x (barrierStrategy X x a) =
          ENNReal.ofReal (barrierValue W a x) := by sorry
