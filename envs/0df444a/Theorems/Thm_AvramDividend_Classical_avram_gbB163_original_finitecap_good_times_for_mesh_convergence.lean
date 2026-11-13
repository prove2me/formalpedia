-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB163_original_finitecap_good_times_for_mesh_convergence
-- name    : AvramDividend.Classical.avram_gbB163_original_finitecap_good_times_for_mesh_convergence
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T12:58:20.610228+00:00
-- url     : https://prove2.me/theorems/f4bd6e4f-4ec1-475b-a4e3-9c1ae70d3e06
-- title:
--   Original Gaussian physical times avoid reserve discontinuities and clipping boundaries a.e
-- statement:
--   On almost every original Gaussian path and almost every positive physical time, the postpayment reserve is continuous, avoids both clipping boundaries, and avoids the stopping time; where it lies inside the C2 clipping band the derivative is continuous. This is the precise a.e regularity reduction from original fixed-level occupation B100 and original path discontinuity results B80/B109.
-- source:
--   Proved B80/B109, Open B100 original fixed-level occupation, smooth clipping

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_gbB163_original_finitecap_good_times_for_mesh_convergence
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
      ContinuousAt (fun s : ℝ => Y (Real.toNNReal s) ω) t ∧
      Y (Real.toNNReal t) ω ≠ a ∧
      Y (Real.toNNReal t) ω ≠ b ∧
      t ≠ (ρ ω : ℝ) ∧
      (Y (Real.toNNReal t) ω ∈ Ioo a b →
        ContinuousAt (deriv w) (Y (Real.toNNReal t) ω)) := by sorry
