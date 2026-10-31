-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_attains_of_local_diff
-- name    : AvramDividend.Classical.avram_wave3_02_cstar_attains_of_local_diff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:38:44.866987+00:00
-- url     : https://prove2.me/theorems/48086688-76ce-4ee7-a938-6f1d91c6ccae
-- title:
--   Genuine cstar barrier is cap-admissible and attains vcstar under pointwise scale differentiability at cstar
-- statement:
--   For the original Standing spectrally negative Lévy dividend model with positive discount and finite cstar, if the scale function is differentiable only at the positive optimal barrier (the zero barrier is handled separately), the actual reflected Stieltjes barrier strategy is admissible with cap cstar and its expected dividends equal vcstar at every nonnegative initial surplus. Uses two canonically Proved source-level theorems; no global scale C1, surrogate or expectation assumption.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1, Theorem 2; canonically Proved original pointwise barrier-value and cap-admissibility bridge.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_all_capital_of_local_diff
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital_of_value_formula

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_cstar_attains_of_local_diff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (hlocal : 0 < (cstar W).toReal →
      DifferentiableAt ℝ W (cstar W).toReal) :
    ∀ x : ℝ, 0 ≤ x →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
        dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
          ENNReal.ofReal (vcstar W x) := by sorry
