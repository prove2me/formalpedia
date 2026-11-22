-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_original_allnu_finitecap_canonical_stopped_full_reward_L1
-- name    : AvramDividend.Classical.avram_jump6_original_allnu_finitecap_canonical_stopped_full_reward_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T21:06:01.999928+00:00
-- url     : https://prove2.me/theorems/bdc679ac-2d2e-4748-a9b4-6369134d673b
-- title:
--   All Lévy jump-activity finite-cap physical ruin-clipped stopped terminal and inclusive dividend cash are integrable and initial event measurable
-- statement:
--   For any original spectrally negative Lévy process, including finite and infinite negative jump activity, and arbitrary admissible strategy at a finite dividend cap, the exact physical ruin-clipped stopped terminal is strongly measurable almost everywhere and L1, inclusive original pre-ruin cash is L1, their sum is L1, and the positive-clock event is measurable in the right-continuous time-zero sigma algebra. No HJB, finite-activity, bounded-variation or Gaussian assumption is needed. This directly discharges the original finite-cap source integrability and measurability parts of both root-positive-clock expected-budget branches while preserving their exact post-right-dividend and ruin-contact conventions.
-- source:
--   Proved canonical stopped source 48783265-ab89-4afd-8565-94268c6b769a, Proved original allnu finitecap terminal ec593f32-19d1-4d88-94a9-80feadfe9005, Proved initial-event source bce62e25-5d97-4357-a119-bc3b8c8eeaa9. Source budgets 15815eff-2c54-41e3-97a6-d216a3efb8d8 and 464200c8-be79-47cd-8938-79343e0d7fce.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_canonical_true_stopped_reward_measurable_Cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_any_stopped_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_original_allnu_finitecap_canonical_stopped_full_reward_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    AEStronglyMeasurable Term P ∧
    Integrable Cash P ∧
    Integrable Term P ∧
    Integrable (fun ω => Term ω + Cash ω) P ∧
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | τ ω ≠ 0} := by sorry
