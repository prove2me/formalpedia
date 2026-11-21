-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_gledger37_positive_uniform_contact_sharp
-- name    : AvramDividend.Classical.avram_agentB_gledger37_positive_uniform_contact_sharp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:09:55.833757+00:00
-- url     : https://prove2.me/theorems/21c1b687-affd-4a0d-9748-a27fc1659f9a
-- title:
--   Positive original stopped physical-grid contact bound for all finite mesh sizes, including first cell
-- statement:
--   The exact original physical-grid initial right-dividend contact, intermediate actual postpayment reserve contacts, terminal reserve contact and pre-ruin strict Stieltjes cash have nonnegative part at most q times the true uniform grid width times original strict dividend measure plus original discounted cash in the NNReal-clamped last strip. The m=0 case is the proved single clipped interval lemma; every m>0 is the proved full-clock sharp stopped contact source with index m-1. Hence this is the missing explicit contact estimate for gledger37 at all mesh sizes.
-- source:
--   Proved avram_agentB_topcap_single_clipped_cell_cash_contact_sharp_v2; newly proved sharp positive-clock source avram_agentB_topcap_stopped_dividend_contact_sharp_nnstrip; original stopping horizon and NNReal truncated subtraction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentB_gledger37_positive_uniform_contact_sharp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Contact : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      (w (x - rightLimit D 0 ω) - w x) +
        Finset.sum (Finset.range (m + 1)) (fun i =>
          E (v (i + 1)) *
            ((w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
              (w (Y (v (i + 1))) - w (riskProcess X x D (v (i + 1)) ω)))) +
        E (ρ ω) * (w (riskProcess X x D (ρ ω) ω) - w (Y (ρ ω))) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      q * (Δ : ℝ) * (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω - Δ : ℝ≥0) : ℝ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    ∀ m : ℕ, ∀ᵐ ω ∂P, 0 < ρ ω → max (Contact m ω) (0 : ℝ) ≤ B m ω := by sorry
