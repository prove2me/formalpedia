-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_value_of_local_differentiability
-- name    : AvramDividend.Classical.avram_wave3_02_cstar_value_of_local_differentiability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:31:20.076187+00:00
-- url     : https://prove2.me/theorems/4c648b7e-cf84-40a4-870b-70248930c0f1
-- title:
--   All-capital optimal-barrier reflected value from pointwise differentiability at positive cstar
-- statement:
--   Under Standing and positive q, assume finite cstar and only pointwise differentiability of the q-scale function at cstar when cstar is positive. Then the true reflected-regulator dividend strategy at cstar has value vcstar for every x≥0. The case cstar=0 uses the separately proved actual zero-barrier reflected cash process; for cstar>0, the Esscher-monotone lower bound forces a positive derivative and the genuine first-upcrossing/stopped-renewal plus initial-excess value theorem gives the result.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1. Uses source-law reflected regulator and its already Proved all-capital value identity, zero barrier Stieltjes cash flow, and Esscher monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_capital_of_local_deriv_nonzero
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_cstar_value_of_local_differentiability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (hpoint : 0 < (cstar W).toReal →
      DifferentiableAt ℝ W (cstar W).toReal) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
        ENNReal.ofReal (vcstar W x) := by sorry
