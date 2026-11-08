-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_upcross_rewards_eventually_exact
-- name    : AvramDividend.Classical.avram_ubv_top9_original_upcross_rewards_eventually_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:38:59.982232+00:00
-- url     : https://prove2.me/theorems/d8be0919-bae6-4bf7-82cd-0a2bb388e942
-- title:
--   True original upper-exit stopped rewards eventually equal arbitrary bounded-clock reward including atoms
-- statement:
--   At each arbitrary bounded right-continuous original stopping time, the true upward-exit localisers are stopping times, uniformly upper bound the original Lévy value, and their exact source discounted post-right-payment terminal plus closed clock Stieltjes cash is eventually literally equal to the original stopped reward path by path.
-- source:
--   Source exact combination of Proved b2e939f7 original any clock upcross localisation and source F expression, no finite cap or limiting UI assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_upcross_rewards_eventually_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℝ≥0)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ n)
    (x q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    ∃ (κ : ℕ → Ω → ℝ≥0) (H : ℕ → Ω → ℝ),
      (∀ j, IsStoppingTime 𝓕.rightCont
        (fun ω => (κ j ω : WithTop ℝ≥0))) ∧
      (∀ j ω, κ j ω ≤ ρ ω) ∧
      (∀ j ω, X.X (κ j ω) ω ≤ (j : ℝ) + 1) ∧
      (∀ j ω, H j ω =
        Real.exp (-(q * (κ j ω : ℝ))) *
          w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
            else riskProcess X x D (κ j ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, ∀ᶠ j : ℕ in atTop, H j ω = F ω) := by sorry
