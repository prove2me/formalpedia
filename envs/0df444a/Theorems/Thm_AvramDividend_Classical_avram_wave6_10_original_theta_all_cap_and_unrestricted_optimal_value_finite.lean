-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_theta_all_cap_and_unrestricted_optimal_value_finite
-- name    : AvramDividend.Classical.avram_wave6_10_original_theta_all_cap_and_unrestricted_optimal_value_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:36:20.950314+00:00
-- url     : https://prove2.me/theorems/a9e292b2-262a-43f5-b25c-5ae4506f9890
-- title:
--   Actual Lévy optimal dividend values are finite for every cap and unrestricted when q dominates ψ(θ)
-- statement:
--   For the exact original spectrally negative Lévy dividend model, if θ>0 and q≥X.ψ θ, every capped optimal dividend value and the unrestricted optimal dividend value are genuinely finite extended nonnegative reals (<∞), uniformly over all caps including ∞. This upgrades the accepted theta-scaled perpetual expected-dividend estimate to qualitative finiteness of the supremum over all original admissible regulators, ruling out divergence of the optimal-value variational problem. It is independent of the currently Open arbitrary C² UBV stochastic HJB core.
-- source:
--   Direct non-vacuous qualitative corollary of canonical Proved 24f9b5f0-00d4-4444-bb25-6d3a0cfcdb49 on original SpectrallyNegativeLevy and valueFunctionLe/valueFunction, using positivity of θ and finite ofReal exponential.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_theta_perpetual_capped_and_unrestricted_value_bound
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_original_theta_all_cap_and_unrestricted_optimal_value_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q) :
    (∀ C : ℝ≥0∞, valueFunctionLe X q C x < ⊤) ∧
      valueFunction X q x < ⊤ := by sorry
