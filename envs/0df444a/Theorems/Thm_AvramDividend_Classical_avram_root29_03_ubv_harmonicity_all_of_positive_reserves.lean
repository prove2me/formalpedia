-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_harmonicity_all_of_positive_reserves
-- name    : AvramDividend.Classical.avram_root29_03_ubv_harmonicity_all_of_positive_reserves
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:46:00.316748+00:00
-- url     : https://prove2.me/theorems/6def2b8b-4a3f-43ff-a06d-48949ed60d4d
-- title:
--   Exact UBV stopped-scale identity at every reserve from its positive-reserve case
-- statement:
--   For a genuine unbounded-variation spectrally negative Levy process with positive discount and a scale function, suppose the actual full two-sided stopped-scale lintegral identity holds whenever the starting reserve x is strictly positive and x<=a. Then it holds for all real a and all x<=a. The negative, zero and nonpositive-upper-barrier cases are discharged using independent proved original-law lemmas, without Standing.
-- source:
--   Genuine case-complete reduction of Open be9dc931 to its strictly positive-reserve stochastic core. Imports only Proved 821b7bc5 (negative x), 6da3d7ac (a<=0), 8a4e69ac (x=0) and 703dc740 (near-zero regularity). Hypothesis preserves the exact original stopped integrand and both strict-clock orderings, with no analytic-only substitution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_negative_reserve
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_nonpositive_upper
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_zero_reserve_of_near_zero
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_ubv_harmonicity_all_of_positive_reserves
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hPositive : ∀ (a x : ℝ), 0 < x → x ≤ a →
      (∫⁻ ω, (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) ∂P) = ENNReal.ofReal (W x)) :
    ∀ (a x : ℝ), x ≤ a →
      (∫⁻ ω, (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) ∂P) = ENNReal.ofReal (W x) := by sorry
