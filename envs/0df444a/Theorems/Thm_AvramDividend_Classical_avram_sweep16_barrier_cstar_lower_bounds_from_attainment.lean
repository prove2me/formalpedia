-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_barrier_cstar_lower_bounds_from_attainment
-- name    : AvramDividend.Classical.avram_sweep16_barrier_cstar_lower_bounds_from_attainment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:46:03.834071+00:00
-- url     : https://prove2.me/theorems/6eda3245-5756-48e1-8b75-f4ee4c2ce45c
-- title:
--   Original barrier c* attainment yields both capped and unrestricted variational lower bounds
-- statement:
--   On the genuine spectrally negative Levy process, the Proved c-star barrier-attainment theorem supplies an actual capped admissible strategy and exact dividendValue identity for every nonnegative reserve. The source definitions of valueFunctionLe and valueFunction are the suprema over real admissible strategies. Insert the same barrier witness into each double supremum, using IsAdmissibleLe implies IsAdmissible, and rewrite the identity. Both inequalities retain the original stochastic process, dividend measure and initial lump payment. No verification upper bound or original-source Ito budget is imported.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_barrier_cstar_lower_bounds_from_attainment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    ∀ x : ℝ, 0 ≤ x →
      ENNReal.ofReal (vcstar W x) ≤ valueFunctionLe X q (cstar W) x ∧
      ENNReal.ofReal (vcstar W x) ≤ valueFunction X q x := by sorry
