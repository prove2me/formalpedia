-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_riskProcess_eq_postpayment_reserve_lebesgue_ae
-- name    : AvramDividend.Classical.avram_wave7_18_original_riskProcess_eq_postpayment_reserve_lebesgue_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:27:37.590241+00:00
-- url     : https://prove2.me/theorems/8aa65b65-7ef3-41e8-ada6-01d147e7df9f
-- title:
--   Original pre-payment and post-payment controlled reserves agree at Lebesgue-almost every nonnegative time
-- statement:
--   For every sample path of the original spectrally negative Lévy reserve and original admissible dividend strategy, the set of right-hand dividend jump times is countable (a Proved source theorem), hence null for real Lebesgue measure. Outside those times and for nonnegative real clock t, the exact Proved reserve decomposition shows riskProcess X x D (t.toNNReal) ω equals x+X.X(t.toNNReal)ω-rightLimit D(t.toNNReal)ω. Thus both reserve versions agree Lebesgue almost everywhere along the original path. This is specifically a dt-null interface for Gaussian/ordinary time integrals; it does not identify the Lebesgue-Stieltjes dividend measure with an atomic measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightJump_support_countable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_18_original_riskProcess_eq_postpayment_reserve_lebesgue_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), 0 ≤ t →
      riskProcess X x D t.toNNReal ω =
        x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω := by sorry
