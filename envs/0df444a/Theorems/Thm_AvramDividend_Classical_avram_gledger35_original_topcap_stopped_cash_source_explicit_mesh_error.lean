-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger35_original_topcap_stopped_cash_source_explicit_mesh_error
-- name    : AvramDividend.Classical.avram_gledger35_original_topcap_stopped_cash_source_explicit_mesh_error
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T19:06:56.012198+00:00
-- url     : https://prove2.me/theorems/856a3841-16ac-4d95-ba99-0b7709829417
-- title:
--   Original top-cap stopped cash and prepayment terminal dominated by clipped source plus explicit discount and last-cell errors
-- statement:
--   A pathwise finite-mesh Ito-Stieltjes cash ledger for the original process. On the compact interior prefix, the positive difference between strict stopped cash plus prepayment terminal and the clipped discounted postpayment source sum is bounded by q times mesh width times the original unweighted dividend measure up to the stopped clock, plus only the strict open final-cell discounted dividend mass. The terminal right-payment atom is excluded, and the initial right payment is charged by the admissible secant inequality. This deliberately isolates the finite-cell stochastic ledger from measurable L1 convergence.
-- source:
--   Exact original clipped physical-grid stochastic cash bound needed to close Open gledger32 42bb8ee3 and f77; proof route uses Proved right endpoint cell d27ba81b, strict crossing e5bd6018, last open cell eb1b02a8, secant 6822fd33, four-event ledger ed0d8024 and finite source telescope b820d43c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger35_original_topcap_stopped_cash_source_explicit_mesh_error
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
    let H : Ω → ℝ := fun ω =>
      if ρ ω = 0 then w x else
        Real.exp (-(q * (ρ ω : ℝ))) *
          w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    let S : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))))
    ∀ m : ℕ, ∀ᵐ ω ∂P,
      max (H ω - w x - S m ω) (0 : ℝ) ≤
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let u : ℝ≥0 := ρ ω - Δ
        q * (Δ : ℝ) *
          (dividendMeasure D ω (Ioc (0 : ℝ) (ρ ω : ℝ))).toReal +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo (u : ℝ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by sorry
