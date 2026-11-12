-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb23_original_compact_reward_L1
-- name    : AvramDividend.Classical.avram_jb23_original_compact_reward_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:25:33.493738+00:00
-- url     : https://prove2.me/theorems/bee07694-8f87-4b19-8046-340d37addb06
-- title:
--   Family of original finite-cap stopped rewards is integrable
-- statement:
--   The exact original full closed-cash stopped reward is integrable for every bounded finite-cap right-continuous-filtration stopping time in a family.
-- source:
--   Reusable indexed-clock specialisation of Proved 551934e5, needed for the JB21 conditional physical stopped budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jb23_original_compact_reward_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (κ : ℕ → Ω → ℝ≥0)
    (hκstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ k ω : WithTop ℝ≥0)))
    (hκbound : ∀ k ω, κ k ω ≤ (n : ℝ≥0))
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ k ω, H k ω =
      Real.exp (-(q * (κ k ω : ℝ))) *
        w (if κ k ω = 0 ∨
              (κ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (κ k ω) ω - rightLimit D (κ k ω) ω
          else riskProcess X x D (κ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ k, Integrable (H k) P := by sorry
