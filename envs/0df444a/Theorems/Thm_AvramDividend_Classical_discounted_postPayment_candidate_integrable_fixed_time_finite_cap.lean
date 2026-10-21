-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_postPayment_candidate_integrable_fixed_time_finite_cap
-- name    : AvramDividend.Classical.discounted_postPayment_candidate_integrable_fixed_time_finite_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:51:10.573929+00:00
-- url     : https://prove2.me/theorems/4306837f-2baa-4a15-977e-b1b5f1fad44f
-- title:
--   Every fixed-time discounted terminal candidate is integrable at finite cap
-- statement:
--   For a spectrally negative Lévy process with its IsProbabilityMeasure field, finite real cap c≥0 and admissible strategy, the discounted terminal candidate e^(-qt)w(x+X_t−D_{t+}) is integrable for every deterministic t. The pending adaptedness theorem supplies Borel measurability of w and adaptation of its post-payment composition to the right-continuous filtration. Since this filtration sits inside the ambient measurable sigma algebra, the deterministic-time candidate is measurable. The pending discounted bound provides a common 0≤f(ω)≤B. The pinned MeasureTheory.Integrable.of_mem_Icc, for finite measure P, makes any AEMeasurable real-valued random variable almost surely in [0,B] integrable. This fills deterministic-time measurability and terminal integrability, but makes no claim about a stopped random-time process, Ito's formula or expectation supermartingale inequalities.
-- source:
--   Dependency-gated on Proved discounted_postPayment_candidate_bounded_finite_cap and local_verification_candidate_borel_and_postPayment_adapted. Pinned Integrable.of_mem_Icc exact remote type recovered.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_postPayment_candidate_bounded_finite_cap
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_postPayment_candidate_integrable_fixed_time_finite_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (x c : ℝ) (hc : 0 ≤ c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (t : ℝ≥0) :
    Integrable (fun ω =>
      Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω)) P := by sorry
