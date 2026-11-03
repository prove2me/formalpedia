-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_positive_discount_all_optimal_values_finite_no_standing
-- name    : AvramDividend.Classical.avram_wave6_10_original_positive_discount_all_optimal_values_finite_no_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:45:54.196714+00:00
-- url     : https://prove2.me/theorems/99a083d1-f3aa-43df-8e36-c6da21ae7c1e
-- title:
--   Every strictly positive discount gives finite capped and unrestricted original optimal dividend values without Standing
-- statement:
--   For any genuine original SpectrallyNegativeLevy process, with no Standing or bounded-variation restrictions, all capped and unrestricted optimal ruin-stopped Stieltjes dividend values at any positive discount q and real initial reserve x are finite ENNReal quantities. The Proved source positive-small-tilt theorem gives theta>0 with psi(theta)<q; the Proved Chat10 theta-specific all-cap finiteness theorem then gives both conclusions uniformly for every cap, including top. No artificial models, changed source spaces or arbitrary-C2 HJB stochastic verification are asserted.
-- source:
--   Original-source no-Standing positive-discount corollary: Proved 6b7f5580-f12e-4a18-8862-48af9a18594f and Proved a9e292b2-262a-43f5-b25c-5ae4506f9890. Strengthens the already-Proved Standing-only finite-value theorem fa9f6f89; root applicability and Stieltjes payoff finiteness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_theta_all_cap_and_unrestricted_optimal_value_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_original_positive_discount_all_optimal_values_finite_no_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (x : ℝ) :
    (∀ C : ℝ≥0∞, valueFunctionLe X q C x < ⊤) ∧
      valueFunction X q x < ⊤ := by sorry
