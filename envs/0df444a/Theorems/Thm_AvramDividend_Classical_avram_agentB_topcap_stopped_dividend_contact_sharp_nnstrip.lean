-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_topcap_stopped_dividend_contact_sharp_nnstrip
-- name    : AvramDividend.Classical.avram_agentB_topcap_stopped_dividend_contact_sharp_nnstrip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T00:16:59.161224+00:00
-- url     : https://prove2.me/theorems/c139ed17-e1a2-4387-a45b-df655be4e66e
-- title:
--   Original ruin-stopped full topcap contact bound with sharp mass and nonnegative final cash strip
-- statement:
--   For the exact original positive and zero min(ruin,n) stopped clocks, the full physical-grid postpayment contact correction and original strict discounted cash lie below q times the mesh width times original positive strict dividend mass and the final open cash interval whose lower endpoint is truncated at zero. At zero stopped clock both contact and strict cash vanish. At positive clock this follows from the independently proved finite-mesh interior bound and corrected original cash partition. This is a strict-clock sharp source for gledger37 including m=0.
-- source:
--   Source-exact real Stieltjes contact cells, exact four-event clipped-grid telescope, proved exponential discount Lipschitz lemma 5206c13c, original right-payment atom inequality and terminal strict Iio stopping window.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentB_topcap_stopped_dividend_contact_sharp_nnstrip
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
    ∀ m : ℕ,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
      let v : ℕ → Ω → ℝ≥0 := fun i ω =>
        min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v i ω) ω - rightLimit D (v i ω) ω
      let Z : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
      let F : Ω → ℝ := fun ω =>
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let B : Ω → ℝ := fun ω =>
        let δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
        let T : ℝ :=
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
              Ioo (((ρ ω - ((n : ℝ≥0) / ((m : ℝ≥0) + 2))) : ℝ≥0) : ℝ) (ρ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal
        q * δ * (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal + T
      ∀ᵐ ω ∂P,
        max (
          (w (x - rightLimit D 0 ω) - w x) +
          Finset.sum (Finset.range (m + 2)) (fun i =>
            E (v (i + 1) ω) *
              ((w (riskProcess X x D (v (i + 1) ω) ω) - w (Z i ω)) +
                (w (Y (i + 1) ω) -
                  w (riskProcess X x D (v (i + 1) ω) ω)))) +
          E (ρ ω) * (w (riskProcess X x D (ρ ω) ω) -
            w (x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω)) +
          F ω) (0 : ℝ) ≤ B ω := by sorry
