-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger81_original_stopped_dividend_contact_mesh_correction
-- name    : AvramDividend.Classical.avram_gledger81_original_stopped_dividend_contact_mesh_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:44:04.396206+00:00
-- url     : https://prove2.me/theorems/16e988d7-f9c2-40b3-b698-135a51f31aef
-- title:
--   Original stopped dividend-contact cash correction is bounded by strict mesh error
-- statement:
--   The deterministic pathwise dividend part of the original four-event stopped telescope: initial right payment, all chronological prepayment-to-postpayment dividend value decrements, terminal right-limit correction and strict pre-stop cash are jointly bounded in positive part by the original weighted full strict cash plus final strict open strip mesh error. It involves no Gaussian centring, Taylor expansion or generator. Proved right-endpoint cash, crossing prepayout and secant inequalities are the necessary local steps.
-- source:
--   Genuine pathwise contact-error subobligation of gledger77 23865b8b. The exact four-event identity is already Proved as gledger35 5d82cfe2. The leaf isolates dividend accounting from that identity and provides the explicit strict discounted cash majorant.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger81_original_stopped_dividend_contact_mesh_correction
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
              Ioo ((ρ ω : ℝ) - δ) (ρ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal
        q * δ * Real.exp (q * (n : ℝ)) * F ω + T
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
