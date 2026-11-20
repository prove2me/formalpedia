-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_clock_caplinear_discounted_terminal_integrable
-- name    : AvramDividend.Classical.avram_f6_original_true_clock_caplinear_discounted_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T10:08:26.087543+00:00
-- url     : https://prove2.me/theorems/6652cb58-8813-4cc7-b9a6-b036945a5afb
-- title:
--   Original bounded stopped discounted caplinear terminal is L1 when original reward and inclusive cash are L1
-- statement:
--   For every true original subordinate compact stopping clock, the discounted caplinear continuation of the actual terminal reserve is L1 when the original full stopped reward F(k) and its actual inclusive dividendMeasure cash are integrable. The exact physical identity F=exp(-qσ)V(W)+Cash follows from public Proved original stopped caplinear cash; hence discounted V(W)=F-Cash and inherits integrability. No invented martingale witness or above-cap smoothness. This isolates terminal L1 for optional stopping/physical Ito.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_true_clock_caplinear_discounted_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (Cash : ℕ → Ω → ℝ)
    (hCash : ∀ k ω, Cash k ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hCashI : ∀ k, Integrable (Cash k) P) :
    ∀ k, Integrable (fun ω : Ω =>
      Real.exp (-(q * (σ k ω : ℝ))) *
        (let V : ℝ → ℝ := fun z =>
          if ENNReal.ofReal z ≤ C then w z
          else w C.toReal + (z - C.toReal)
         V (if σ k ω = 0 ∨
           (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
             x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
           else riskProcess X x D (σ k ω) ω))) P := by sorry
