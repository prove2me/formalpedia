-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_bv_contact_proved_sources_for_original
-- name    : AvramDividend.Classical.avram_bridge20261122_bv_contact_proved_sources_for_original
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:51:52.708027+00:00
-- url     : https://prove2.me/theorems/39788d7d-b47e-4fa4-aa95-17b087cfe8f3
-- title:
--   BV positive-horizon stopped HJB with original unique ruin-contact mesh residual certificates
-- statement:
--   BV positive-horizon stopped HJB with original unique ruin-contact mesh residual certificates. The original physical stopped X,D,clock, dividend cash and terminal bound are retained. The additional assumptions are exact source-authentic proven interfaces on this same Levy process (or sample probability measure). The open child must apply these concrete mesh and terminal identities in an actual physical stopped stochastic-budget proof; no claim of the missing Ito or HJB expectation is introduced.
-- source:
--   Accepted root-connected physical Avram parent a19d8b28-f606-4a95-907a-cec601da255f and already-Proved export sources aa8e8474-ec43-4e06-b0c1-fda9cddc285f, fd161e0c-7c5b-40f8-b67b-a3dc0ee989db

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section
open Classical

theorem AvramDividend.Classical.avram_bridge20261122_bv_contact_proved_sources_for_original
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hBvContactSources : (∀ (ω : Ω)
    (n : ℕ) (u : ℕ → ℝ≥0) (τ : ℝ≥0)
    (W : ℕ → ℝ) (E : ℕ → Prop) (hmono : Monotone u)
    (hE : ∀ i, E i → u i < τ),
let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
    let Raw := ∑ i ∈ Finset.range n,
      if E i then W i * (R (u i) - R (u (i + 1))) else 0
    let Stopped := ∑ i ∈ Finset.range n,
      if E i then W i * (R (min (u i) τ) - R (min (u (i + 1)) τ)) else 0
    ∃ t : ℝ, Raw = Stopped + t ∧
      (t = 0 ∨ ∃ i ∈ Finset.range n,
        E i ∧ τ < u (i + 1) ∧
          t = W i * (R τ - R (u (i + 1))))) ∧
      (∀ (n : ℕ) (u : ℕ → ℝ≥0) (τ : ℝ≥0)
    (hmono : ∀ i, i < n + 1 → u i ≤ u (i + 1)),
∀ i j : ℕ, i < n + 1 → j < n + 1 →
      (u i < τ ∧ τ ≤ u (i + 1)) →
      (u j < τ ∧ τ ≤ u (j + 1)) → i = j)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by sorry
