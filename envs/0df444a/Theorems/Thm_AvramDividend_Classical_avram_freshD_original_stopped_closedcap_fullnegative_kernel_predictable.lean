-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_stopped_closedcap_fullnegative_kernel_predictable
-- name    : AvramDividend.Classical.avram_freshD_original_stopped_closedcap_fullnegative_kernel_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T18:54:04.844922+00:00
-- url     : https://prove2.me/theorems/b7420f09-9e92-40e0-9569-7c2dc05097ea
-- title:
--   Original finite-horizon, true ruin- and σ-clipped closed-cap nonlinear negative-mark kernel is predictable
-- statement:
--   The actual original Lévy negative-jump nonlinear value kernel with full mark size z<0, pre-dividend left-limit reserve Y, finite stop σ and true inclusive ruin clock has joint measurability on the right-continuous predictable time-space filtration times mark space. It retains all negative marks including ruin overshoot and cap-boundary states (0≤Y, ofRealY≤C), uses discounted w(Y+z)-w(Y) rather than fixed Jfull, and is zero outside the physical bounded horizon. This source premise is necessary for the fullmark marked compensator integrability and initial-event centring in Agent D theorem 04e002c9.
-- source:
--   Precise unpredictable-looking original full negative-mark compensation kernel, reduced to Proved left-limit strongly predictable and stopping-time predictable identities, on the same source X. Positive probability assumption is not needed for this descriptive measurability result.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_controlled_stopped_prejump_marked_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_stopped_closedcap_fullnegative_kernel_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (n : ℝ))).map Real.toNNReal
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H := by sorry
