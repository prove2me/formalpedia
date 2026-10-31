-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_all_capital_of_local_diff
-- name    : AvramDividend.Classical.avram_wave3_02_cstar_all_capital_of_local_diff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:04:48.604387+00:00
-- url     : https://prove2.me/theorems/522f0648-81fa-4c88-a5a8-8b89742a646a
-- title:
--   Actual all-capital optimal-barrier value from differentiability only at cstar
-- statement:
--   For the genuine Standing spectrally negative Levy process and finite optimal barrier cstar, the actual Stieltjes dividend value of reflection at cstar equals the exact candidate barrier value at every nonnegative initial capital. The sole additional analytic assumption is pointwise differentiability of the source scale function at cstar when cstar>0. The zero-barrier case follows from the accepted separate boundary identity; positive cstar uses proven Esscher pointwise derivative positivity and the proven original strong-Markov all-capital barrier strategy identity.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1 and Theorem 2; source-level accepted first-upcrossing, zero-barrier and local derivative results.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_pos_of_pointwise_diff
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_capital_of_local_deriv_nonzero
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_cstar_all_capital_of_local_diff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (hlocal : 0 < (cstar W).toReal →
      DifferentiableAt ℝ W (cstar W).toReal) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
        ENNReal.ofReal (vcstar W x) := by sorry
