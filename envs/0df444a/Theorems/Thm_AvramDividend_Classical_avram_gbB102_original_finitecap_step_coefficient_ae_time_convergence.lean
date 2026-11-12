-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB102_original_finitecap_step_coefficient_ae_time_convergence
-- name    : AvramDividend.Classical.avram_gbB102_original_finitecap_step_coefficient_ae_time_convergence
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T22:30:09.132919+00:00
-- url     : https://prove2.me/theorems/09371f71-73ed-4e42-9e82-ae3cdda8c272
-- title:
--   Original stopped finite-cap Gaussian gradient step coefficients converge at almost every time
-- statement:
--   For the original X,D,Ω,P and strict preruin stopped clock ρ, the actual finite uniform postpayment clipped-gradient coefficient step at each positive interior time converges almost surely in path and almost everywhere in Lebesgue time to the original continuous-time stopped postpayment coefficient. Exceptional time sets are the original reserve discontinuities (B101/B80), fixed upper clipping level contact (B100), and the single random stopping boundary. The finite-cap interior derivative is continuous on its compact strip, and δ-floor controls the lower clip. This is the genuine source-specific a.e. approximation prerequisite to B65; no new independent process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_gbB102_original_finitecap_step_coefficient_ae_time_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
    (j : ℕ) :
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let a : ℝ := δ / 2
    let Y : ℝ≥0 → Ω → ℝ := fun s ω =>
      x + X.X s ω - rightLimit D s ω
    let H : ℝ → Ω → ℝ := fun t ω =>
      if (Real.toNNReal t) < ρ ω then
        Real.exp (-(q * t)) *
          (if Y (Real.toNNReal t) ω ∈ Icc a b then
            deriv w (Y (Real.toNNReal t) ω) else 1)
      else 0
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then (if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) *
          (if Y (s i) ω ∈ Icc a b then deriv w (Y (s i) ω)
            else 1) else 0)
        else 0)
    ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      Tendsto (fun m : ℕ => K m t ω) atTop (𝓝 (H t ω)) := by sorry
