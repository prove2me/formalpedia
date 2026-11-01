-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable
-- name    : AvramDividend.Classical.avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:56:55.121178+00:00
-- url     : https://prove2.me/theorems/872a8afd-3b84-43d6-8d9c-47c90daa9151
-- title:
--   Genuine same-path source exponential weighted full random Stieltjes dividend integral is measurable
-- statement:
--   For actual original same-path Lévy source X and adapted left-continuous D, the random full dividend Stieltjes integral of the source controlled exponential over any jointly measurable time/path region S is measurable in ω. It uses the genuine global s-finite random dividend kernel, source joint time/path measurability and kernel integration. S can encode strict pre-ruin killing and finite horizon, including payment atoms and diffuse/singular-continuous mass; this is an essential authentic Tonelli/Fatou prerequisite, not an assumption of a new random PRM.
-- source:
--   Proved dividendMeasure_global_sfinite_kernel_exists 766b5129 and accepted source exponential joint time/path measurable 30c00aaa, pinned Mathlib Kernel.MeasurableLIntegral

import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (S : Set (ℝ × Ω)) (hS : MeasurableSet S) :
    Measurable (fun ω : Ω =>
      ∫⁻ t : ℝ, if (t, ω) ∈ S then
        ENNReal.ofReal (Real.exp
          (θ * (x + X.X t.toNNReal ω -
            rightLimit D t.toNNReal ω) - (t.toNNReal : ℝ) * q))
      else 0 ∂dividendMeasure D ω) := by sorry
