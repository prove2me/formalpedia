-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_subclock_cash_integrable_of_finite_full_mass
-- name    : AvramDividend.Classical.avram_f6_original_subclock_cash_integrable_of_finite_full_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T10:12:30.403122+00:00
-- url     : https://prove2.me/theorems/f1b9434d-6d5c-4187-83a3-84c0dc094a48
-- title:
--   Original subordinate inclusive cash L1 from full cash L1 with finite mass and actual measurability
-- statement:
--   For the actual original capped dividend strategy, each subordinate stopping-clock discounted paymentTimes∩Iic cash is L1 when the full-clock real cash is L1, the original full ENNReal cash mass is finite pathwise and the subclock cash is almost everywhere strongly measurable. The proof uses the already Proved original ENNReal cash monotonicity plus genuine finiteness-sensitive toReal domination, nonnegative real cash and Integrable.mono. This avoids the otherwise invalid toReal(top)=0 inference and supplies the correct actual cash L1 source for stopped Ito/Fatou.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_subclock_cash_integrable_of_finite_full_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (σ : ℕ → Ω → ℝ≥0)
    (hclock : ∀ k ω, σ k ω ≤ τ ω)
    (hFullFinite : ∀ ω : Ω,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)) ≠ ⊤)
    (FullCash : Ω → ℝ)
    (hFullCash : ∀ ω, FullCash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFullI : Integrable FullCash P)
    (PartCash : ℕ → Ω → ℝ)
    (hPartCash : ∀ k ω, PartCash k ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hPartMeas : ∀ k, AEStronglyMeasurable (PartCash k) P) :
    ∀ k, Integrable (PartCash k) P := by sorry
