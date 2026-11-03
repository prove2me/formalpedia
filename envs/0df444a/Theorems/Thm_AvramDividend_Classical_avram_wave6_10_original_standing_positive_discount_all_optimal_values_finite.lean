-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_standing_positive_discount_all_optimal_values_finite
-- name    : AvramDividend.Classical.avram_wave6_10_original_standing_positive_discount_all_optimal_values_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:56:02.425456+00:00
-- url     : https://prove2.me/theorems/fa9f6f89-0429-42e8-8ce7-f7089d4ae0f3
-- title:
--   Every positive-discount Standing Lévy optimal dividend value is finite, with or without reserve cap
-- statement:
--   For any original spectrally negative Lévy process satisfying the canonical Standing assumptions, any strictly positive discount q, any initial capital x and any reserve cap C, the genuine capped optimal dividend value and unrestricted optimal value are finite elements of ENNReal. Unlike the antecedent theta-specific estimate, this statement has no extra Laplace-tilt hypothesis: the already proved source-identified positive q-root of the true Lévy exponent supplies θ>0 with ψ(θ)=q, and the already proved Chat10 actual-process theta finiteness bridge applies. It rules out divergent global optimizers in the exact Standing/positive-discount setting used by corrected UBV verification and root optimal-barrier mathematics, without assuming the Open arbitrary C² stochastic HJB core.
-- source:
--   Genuine original Standing SpectrallyNegativeLevy source; direct formally justified bridge of Proved avram_wave4_05_source_positive_psi_root_of_standing (1da68fa5-700c-4631-bdca-58297a897faf) and Proved avram_wave6_10_original_theta_all_cap_and_unrestricted_optimal_value_finite (a9e292b2-262a-43f5-b25c-5ae4506f9890).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_psi_root_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_theta_all_cap_and_unrestricted_optimal_value_finite
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_original_standing_positive_discount_all_optimal_values_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (x : ℝ) :
    (∀ C : ℝ≥0∞, valueFunctionLe X q C x < ⊤) ∧
      valueFunction X q x < ⊤ := by sorry
