-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b27_original_phys_source_ruin_contact_terminal_retained
-- name    : AvramDividend.Classical.avram_b27_original_phys_source_ruin_contact_terminal_retained
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:54:02.652215+00:00
-- url     : https://prove2.me/theorems/a53d8a91-fa7c-472a-ac76-421245a9de22
-- title:
--   The exact original B25 physical stopped cash source retains the discounted unit terminal at continuous ruin contact
-- statement:
--   Under the literal original B25 stopped payoff definition hFsource, at a strictly positive stopping time equal to the physical ruin time with actual risk reserve exactly zero, discounted terminal w(0)=1 and zero physical dividend cash, the payoff is the discounted unit terminal exp(-q sigma), including on the ruin-contact event. This is essential to distinguish the original physical mesh theorem from a different killed-at-ruin strict survival payoff. The theorem never replaces the original risk reserve or payment support.
-- source:
--   Original B25 topcap physical source 78ac3aee and exact published riskProcess, ruinTime, rightLimit and paymentTimes definitions; corrected 15 November 2026 Brownian/Poisson no-jump source obstruction audit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_b27_original_phys_source_ruin_contact_terminal_retained
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) (hσ : 0 < σ ω)
    (hContact : (σ ω : ℝ≥0∞) = ruinTime X x D ω)
    (hReserve : riskProcess X x D (σ ω) ω = 0)
    (hw0 : w 0 = 1)
    (hZeroCash :
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal = 0) :
    F ω = Real.exp (-(q * (σ ω : ℝ))) := by sorry
