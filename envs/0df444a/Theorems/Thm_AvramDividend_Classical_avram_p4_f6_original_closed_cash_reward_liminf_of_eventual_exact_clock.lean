-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_closed_cash_reward_liminf_of_eventual_exact_clock
-- name    : AvramDividend.Classical.avram_p4_f6_original_closed_cash_reward_liminf_of_eventual_exact_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:18:01.493757+00:00
-- url     : https://prove2.me/theorems/3e407d7c-f4eb-4175-84ff-912f395f52c7
-- title:
--   Original source physical stopped reward has exact liminf once local clocks eventually coincide with natural clock
-- statement:
--   If a cofinal compact localisation of the original stopped Lévy dividend process eventually has exactly the natural clock almost surely, the exact right-limit reserve, closed Iic Stieltjes cash including time-zero and horizon atoms, and discounted terminal yield eventual equality of physical rewards. Their ENNReal liminf therefore equals the natural stopped payoff almost surely. No local martingale uniform integrability or extraneous process is assumed.
-- source:
--   Same-source substitution into original physical stopped W, discounted terminal, Iic dividend measure, followed by Filter.liminf_congr and liminf_const.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_original_closed_cash_reward_liminf_of_eventual_exact_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
        else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hcofinal : ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, σ k ω = τ ω) :
    ∀ᵐ ω ∂P, ENNReal.ofReal (Term ω + Cash ω) =
      Filter.liminf (fun k => ENNReal.ofReal (F k ω)) atTop := by sorry
