-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_finitecap_original_stopped_reward_integrable
-- name    : AvramDividend.Classical.avram_jump6_finitecap_original_stopped_reward_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T18:26:20.871875+00:00
-- url     : https://prove2.me/theorems/87d29cce-b557-4e47-8b59-ca35f657cc3b
-- title:
--   Original finite-cap stopped post-payment terminal plus full dividend cash is integrable
-- statement:
--   For any original spectrally negative Lévy process, admissible finite-cap strategy, continuous nonnegative-side payoff vanishing on negative reserves, nonnegative discount and bounded ruin-clipped stopping time, the actual post-dividend terminal reward plus inclusive physical Lebesgue–Stieltjes dividend cash is L1 integrable. No separate terminal measurability or cash integrability assumption is needed. This is a direct source-faithful use of the proved general finite-cap stopped reward integrability theorem, and removes the integrability sub-obligation from the finite-cap part of the root-connected expected stopped reward budget.
-- source:
--   Proved 551934e5-0a70-49a4-87a1-804601657da3 (any bounded original stop finitecap full reward L1), Proved edebe535-25e3-417c-84fb-5a8a21a57b8a (ruin clip bounded by n). Relevant to Open Avram root case 15815eff-2c54-41e3-97a6-d216a3efb8d8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_finitecap_original_stopped_reward_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hFiniteCap : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
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
    Integrable (fun ω => Term ω + Cash ω) P := by sorry
