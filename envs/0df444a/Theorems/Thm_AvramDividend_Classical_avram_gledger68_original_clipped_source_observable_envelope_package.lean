-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger68_original_clipped_source_observable_envelope_package
-- name    : AvramDividend.Classical.avram_gledger68_original_clipped_source_observable_envelope_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:15:52.23647+00:00
-- url     : https://prove2.me/theorems/bc286646-e3ed-4a02-be6c-90289e483e61
-- title:
--   Exact original stopped Gaussian source has measurable cells, exponential terminal L1 and a one-sided value envelope
-- statement:
--   For each fixed original random-clipped deterministic mesh, isolate the genuinely stochastic and measurable facts needed to dominate the physical source: finite underlying probability measure, source a.e. measurability, positive discounts at most one, inactive zero cells, active compact lower/exponential upper value envelopes, and stopped Gaussian exponential moments for every original cell endpoint. This removes the final finite-sum integration algebra, already Proved as gledger66.
-- source:
--   Root-connected necessary physical-observables child for gledger53. Reuse Proved gledger54 stopped prepayment floor, gledger63 compact lower, gledger65 HJB upper, gledger62 stopped exponential L1, and gledger67 clipped stopping clocks. Parent gledger53 is closed by gledger66 analytic finite-sum domination after this package.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger68_original_clipped_source_observable_envelope_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ m : ℕ,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → Ω → ℝ≥0 := fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℕ → Ω → ℝ := fun i ω => Real.exp (-(q * (v i ω : ℝ)))
      let Y : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v i ω) ω - rightLimit D (v i ω) ω
      let Z : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
      let S : Ω → ℝ := fun ω => Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * w (Y i ω) +
        E (i + 1) ω * (w (Z i ω) - w (Y i ω)))
      ∃ (hFinite : IsFiniteMeasure P), ∃ θ K b : ℝ,
        0 ≤ K ∧ 0 ≤ b ∧
        AEStronglyMeasurable S P ∧
        (∀ ω i, 0 ≤ E i ω) ∧
        (∀ ω i, E i ω ≤ 1) ∧
        (∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
          (E (i + 1) ω = E i ω ∧ Z i ω = Y i ω) ∨
          (-b ≤ w (Y i ω) ∧
            w (Z i ω) ≤ K * Real.exp (θ * Z i ω))) ∧
        (∀ i ∈ Finset.range (m + 1),
          Integrable (fun ω => Real.exp (θ * Z i ω)) P) := by sorry
