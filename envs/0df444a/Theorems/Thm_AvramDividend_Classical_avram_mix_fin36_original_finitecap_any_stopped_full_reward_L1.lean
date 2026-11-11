-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
-- name    : AvramDividend.Classical.avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:36:22.989685+00:00
-- url     : https://prove2.me/theorems/551934e5-0a70-49a4-87a1-804601657da3
-- title:
--   Any bounded original finite-cap ruin-clipped full stopped reward is integrable
-- statement:
--   For the original spectrally negative Lévy process and any admissible dividends with finite cap, the complete discounted postpayment-or-ruin terminal reward plus closed dividend cash at an arbitrary bounded original right-continuous stopping time is Lebesgue integrable. This includes initial dividend, positive pre-ruin payments, ruin and horizon atoms, under no finite first absolute jump-size assumption. It is proved from the existing original bounded-clock full-cash L1, source measurability and family L1-transfer theorems.
-- source:
--   Root-connected missing integrability bridge for Open 52a16569; reuses Proved 3deca135, 05fe4611 and 48f8c2db. Direct finite cap physical reward integrability without assuming it as a hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (G : Ω → ℝ)
    (hGsource : ∀ ω, G ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨
              (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    Integrable G P := by sorry
