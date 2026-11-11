-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite62_original_cap_strip_occupation_measurable_ae_vanish
-- name    : AvramDividend.Classical.avram_gfinite62_original_cap_strip_occupation_measurable_ae_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:35:27.525944+00:00
-- url     : https://prove2.me/theorems/7b79e93d-d958-42c0-bc38-43dbd921f5db
-- title:
--   Original stopped cap strip measurable bounded and almost surely vanishing
-- statement:
--   On the original controlled stopped reserve and initial event, prove joint measurability of upper-cap strip occupation, a uniform deterministic bound by the horizon n, and pathwise a.e. convergence to zero as cutoffs approach cap. The cap-contact null-time proof is already available; this is the exact pathwise and measurability input to DCT for expected occupation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite62_original_cap_strip_occupation_measurable_ae_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      let b : ℕ → ℝ := fun j =>
        C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Occ : ℕ → Ω → ℝ := fun j ω =>
        ∫ t in Ioo (0 : ℝ) (n : ℝ),
          if t < (ρ ω : ℝ) ∧
              b j < riskProcess X x D (Real.toNNReal t) ω
          then (1 : ℝ) else 0 ∂volume
      (∀ j : ℕ, AEStronglyMeasurable
        (A.indicator (Occ j)) P) ∧
      (∀ j : ℕ, ∀ ω : Ω,
        ‖A.indicator (Occ j) ω‖ ≤ (n : ℝ)) ∧
      (∀ᵐ ω ∂P,
        Tendsto (fun j : ℕ => A.indicator (Occ j) ω)
          atTop (𝓝 (0 : ℝ))) := by
  sorry
