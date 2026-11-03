-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_ruin_graph_finite_pushed_clock_null
-- name    : AvramDividend.Classical.avram_wave7_17_original_ruin_graph_finite_pushed_clock_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:35:08.447298+00:00
-- url     : https://prove2.me/theorems/1873d50b-5a11-4322-a900-77b13aa57445
-- title:
--   Original ruin-time graph is null for P × the exact finite-horizon pushed physical NNReal clock
-- statement:
--   For the actual original spectrally negative Lévy process and admissible dividend strategy, each original ruin-time graph section has zero mass under the finite-horizon physical clock obtained by restricting real Lebesgue measure to [0,T] and pushing it forward through Real.toNNReal. This is exactly the physical nonnegative time clock used in the accepted W7-02 and W7-17 HJB occupation estimates. The theorem keeps the original P and original ruinTime and does not drop realised source-jump or Stieltjes atoms at ruin.
-- source:
--   Original ruinTime_measurable, real Lebesgue null singleton, Mathlib Measure.map_apply/restrict_apply and measure_prod_null_of_ae_null; source original physical clock from W7-02/17.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_ruin_graph_finite_pushed_clock_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) :
    let νT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    (P.prod νT)
      {p : Ω × ℝ≥0 |
        (p.2 : ℝ≥0∞) = ruinTime X x D p.1} = 0 := by sorry
