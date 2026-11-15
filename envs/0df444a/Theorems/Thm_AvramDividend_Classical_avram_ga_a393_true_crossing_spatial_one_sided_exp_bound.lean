-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a393_true_crossing_spatial_one_sided_exp_bound
-- name    : AvramDividend.Classical.avram_ga_a393_true_crossing_spatial_one_sided_exp_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:38:23.62384+00:00
-- url     : https://prove2.me/theorems/ea03d453-3089-4e3d-aa09-27018f4aa155
-- title:
--   Original strictly crossing Gaussian spatial discounted value one-sided exponential running supremum bound
-- statement:
--   The positive discounted original spatial value increment on every genuinely strict crossing cell has a single fixed-horizon exponential running-supremum bound, with common nonnegative coefficients and additive constant, uniformly across meshes.
-- source:
--   Avram Gaussian A a387, using Proved a45 full stopped source cell envelope and Proved a44 discounted positive spatial domination.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a393_true_crossing_spatial_one_sided_exp_bound
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
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ θ K b : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧ 0 ≤ b ∧
      ∀ (m : ℕ), ∀ᵐ ω ∂P, ∀ (i : ℕ), i < m →
        (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω →
        ρ ω < ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
          (n : ℝ≥0) / ((m : ℝ≥0) + 1)) →
        max (Real.exp (-(q * (ρ ω : ℝ))) *
          (w (x + X.X (ρ ω) ω -
              rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω) -
           w (x + X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
              rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω))) 0 ≤
          K * Real.exp (θ * runningSup X (n : ℝ≥0) ω) + b := by sorry
