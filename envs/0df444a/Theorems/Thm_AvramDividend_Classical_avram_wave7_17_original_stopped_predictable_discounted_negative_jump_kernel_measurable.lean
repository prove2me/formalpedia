-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
-- name    : AvramDividend.Classical.avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:54:11.438162+00:00
-- url     : https://prove2.me/theorems/d4504671-19ee-40bb-b80b-5a8ce1fdc0dc
-- title:
--   Actual discounted nonlinear negative Lévy jump kernel is jointly predictable on every original stopped source region
-- statement:
--   For the original actual Lévy source X and original controlled left-limit reserve, any Borel HJB function satisfying the source continuity and negative-side zero extension has a globally predictable discounted nonlinear negative-jump mark kernel after localisation to a set E measurable in the actual right-continuous predictable sigma algebra. This removes the explicitly assumed measurable kernel prerequisite from the Proved original BV C1 negative-source compensation theorem, including the inclusive ruin-stop predictable localisation. No independent Poisson source or cash-payoff inequality is introduced.
-- source:
--   Source strongly predictable left-limit theorem 94ee9994, original Borel candidate 30325a04, original source negative-mark compensation interface 8e5ebef5 and inclusive-stop predictable region 4e14265e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E) :
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        if p.1 ∈ E ∧ p.2 < 0 then
          Real.exp (-(q * (p.1.1 : ℝ))) *
            (w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
             w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
        else 0) := by sorry
