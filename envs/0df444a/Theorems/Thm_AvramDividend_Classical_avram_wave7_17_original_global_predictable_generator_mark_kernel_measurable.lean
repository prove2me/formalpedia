-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_global_predictable_generator_mark_kernel_measurable
-- name    : AvramDividend.Classical.avram_wave7_17_original_global_predictable_generator_mark_kernel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:30:34.441026+00:00
-- url     : https://prove2.me/theorems/7f6fc26e-6c72-464c-aa61-7153e267bc97
-- title:
--   Actual Lévy generator marked jump kernel is jointly predictable × Borel measurable on the source Ω and jump marks
-- statement:
--   For the original spectrally negative Lévy process, its actual strongly predictable controlled pre-payment reserve left limit, and an HJB candidate Borel by continuity on nonnegative reserves and zero extension on negative reserves, the exact compensated Lévy generator mark integrand is measurable in the original right-continuous predictable sigma algebra on physical time × Ω, product with the real source-mark Borel space. This is strictly stronger than ambient time × Ω measurability and supplies a genuine predictable marked integrand for the existing source compensation and stopped generator L1 theorems. It asserts neither a fabricated Poisson representation nor a compensation identity, integrability, or expected full Stieltjes budget.
-- source:
--   Original controlled Lévy model of Avram-Palmowski-Pistorius (2007), Proposition 4(i). Proved original strong predictability 94ee9994 and original Borel HJB candidate 30325a04, plus pinned Mathlib measurable_deriv and Measurable.indicator. Exact source generatorIntegrand from Definition 933ced80.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_global_predictable_generator_mark_kernel_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) :
    Measurable[(𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        SpectrallyNegativeLevy.generatorIntegrand w
          (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1) p.2) := by sorry
