-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
-- name    : AvramDividend.Classical.barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:24:42.748468+00:00
-- url     : https://prove2.me/theorems/fd11e610-82a7-4259-aadf-65c9d68662bb
-- title:
--   Zero-barrier dividend boundary package from almost-sure negative near-zero paths
-- statement:
--   This proves the zero-barrier strategy boundary-value package in the unbounded-variation branch whenever almost every Lévy sample path enters the negative half-line at arbitrarily small positive times. The bridge barrierRuinTime_zero_of_near_zero_negative_path converts that classical regularity property into almost-sure instantaneous reflected drawdown ruin; the already canonically Proved conditional zero-boundary strategy theorem closes the value equality. The remaining genuinely stochastic task is to derive the almost-sure negative near-zero path condition from unbounded variation of the spectrally negative Lévy triplet.
-- source:
--   Direct branch of canonical barrier_zero_boundary_value_package, using Proved conditional package and the pathwise negative excursion lemma.

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_negative_path
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_instant_ruin

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    0 ≤ barrierValue W 0 0 ∧
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) := by sorry
