-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_origin_dyadic_deficit_zero_ae_ws01c
-- name    : AvramDividend.Classical.bv_actual_origin_dyadic_deficit_zero_ae_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:36:03.35357+00:00
-- url     : https://prove2.me/theorems/4809db25-cae9-433f-b7f2-25a2a48cd94a
-- title:
--   Actual BV Lévy origin dyadic deficit slopes converge to zero almost surely
-- statement:
--   For the actual bounded-variation spectrally negative Lévy process, the entire sequence of dyadic residual slopes d−(X_(2^(-n))−X_0)/2^(-n) converges almost surely to zero. This is the correct Cauchy upgrade: the source-complete Fubini-stationarity theorem gives an almost-sure Cauchy sequence, the actual scaled-tail theorem gives convergence in measure, and the already Proved Cauchy-plus-in-measure limit theorem yields the full almost-sure zero limit. This avoids the false inference of almost-sure convergence from convergence in probability alone.
-- source:
--   Source-complete WS01C origin zero-slope formalisation assembled from work/avram_ws01c_origin_zero_slope_full_assembly_draft.lean. Invokes existing canonical Proved Cauchy-plus-measure theorem eb4d928e, plus two newly submitted specific actual-process intermediate targets.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_origin_dyadic_cauchy_ae_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_dyadic_slope_tendstoInMeasure_zero_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_ae_cauchy_plus_in_measure_bundle_ws01c

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.bv_actual_origin_dyadic_deficit_zero_ae_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        X.drift -
          (X.X (((1 : ℝ≥0) / 2) ^ n) ω - X.X 0 ω) /
            (((1 : ℝ≥0) / 2) ^ n : ℝ))
        atTop (𝓝 (0 : ℝ)) := by sorry
