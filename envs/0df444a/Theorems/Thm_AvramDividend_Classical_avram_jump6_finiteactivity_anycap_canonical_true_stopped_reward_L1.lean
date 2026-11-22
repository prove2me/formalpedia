-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_finiteactivity_anycap_canonical_true_stopped_reward_L1
-- name    : AvramDividend.Classical.avram_jump6_finiteactivity_anycap_canonical_true_stopped_reward_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T19:56:14.462144+00:00
-- url     : https://prove2.me/theorems/73063794-0c7f-401f-b376-d948b8ae0085
-- title:
--   Finite-activity original UBV HJB exact stopped full reward is L1 for every cap, with canonical terminal measurability
-- statement:
--   For the original unbounded-variation finite-jump-activity spectrally negative Lévy source, HJB max equation, any positive finite or infinite cap, arbitrary admissible original dividend strategy and exact integer ruin-clipped stopping time, show the actual post-right-dividend terminal is almost everywhere strongly measurable, inclusive original discounted dividend cash and terminal are both L1, their sum is L1, and the positive-stop event belongs to the original right-continuous initial sigma-algebra. No source measurability or cash integrability is separately assumed: these follow from the Proved canonical stopped-reward existence theorem by pointwise uniqueness. Finite cap uses the Proved reward-L1 source preflight; infinite cap uses HJB growth and original-X exponential stopped terminal envelope. The remaining source for original positive-clock expected budget is strictly the nonlinear Ito-Meyer upper expectation.
-- source:
--   Root exact expected budget 15815eff, finitecap source Proved 574fad72, forthcoming topcap direct source 7d0ba210 candidate 45212, forthcoming canonical W/Cash/Term source publication 4391f52d. Both pending theorem statuses must become Proved before attempting this theorem's publication and compilation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_canonical_true_stopped_reward_measurable_Cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_jump6_finitecap_activity_root_budget_source_preflight
import Theorems.Thm_AvramDividend_Classical_avram_jump6_finiteactivity_topcap_HJB_actual_stopped_full_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_finiteactivity_anycap_canonical_true_stopped_reward_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxpos : 0 < x)
    (k : ℕ) (hk : 0 < k)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
 :
    AEStronglyMeasurable Term P ∧
    Integrable Cash P ∧
    Integrable Term P ∧
    Integrable (fun ω => Term ω + Cash ω) P ∧
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | τ ω ≠ 0} := by sorry
