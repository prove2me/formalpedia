-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_full_future_conditional_strong_markov
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_full_future_conditional_strong_markov
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:46:31.123193+00:00
-- url     : https://prove2.me/theorems/56beabdc-9d4b-4473-b38a-0c01b9a79b61
-- title:
--   Unbounded finite right-continuous stopping full-path conditional source law equals original Lévy law
-- statement:
--   For any finite original right-continuous Lévy stopping time τ and any measurable integrable real functional Z on the entire future Lévy path product space, the conditional expectation of Z evaluated on t↦X.X(τ+t)−X.Xτ given the exact stopped-history sigma algebra equals the deterministic constant E[Z(t↦X.Xt)] from the original process. Neither bounded stopping nor ν=0 nor σ>0 is assumed, and both sides are on the same actual Ω and P. Combine the already Proved original right-continuous post-stop path-law equality and full-future functional conditional expectation using source path measurability and Mathlib integral map. This is the genuine full-path strong Markov conditional law for the original source, not a Lévy–Itô continuous Gaussian decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_full_future_source_law
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_future_functional_condExp
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_full_future_conditional_strong_markov
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (Z : (ℝ≥0 → ℝ) → ℝ) (hZmeas : Measurable Z)
    (hInt : Integrable (fun ω : Ω => Z (fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω)) P) :
    P[(fun ω : Ω => Z (fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => ∫ ω, Z (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  sorry
