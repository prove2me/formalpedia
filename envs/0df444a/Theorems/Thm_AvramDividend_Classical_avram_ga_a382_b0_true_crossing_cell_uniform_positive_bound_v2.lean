-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a382_b0_true_crossing_cell_uniform_positive_bound_v2
-- name    : AvramDividend.Classical.avram_ga_a382_b0_true_crossing_cell_uniform_positive_bound_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:53:11.91655+00:00
-- url     : https://prove2.me/theorems/82fc1007-4671-4113-950d-ca498b4de21d
-- title:
--   Source-exact uniform positive bound tending to zero for the single true stopped Gaussian crossing cell
-- statement:
--   Under the original stopped zero-jump Gaussian admissibility and positive compact prefix, the positive compensated residual in any genuinely crossing physical cell is bounded by a common nonnegative pathwise mesh error that tends to zero almost surely.
-- source:
--   Exact cross-cell source a138, Proved abstract finite-grid bound a141, continuous Gaussian source modulus a102/a106 and compensation a112.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a382_b0_true_crossing_cell_uniform_positive_bound_v2
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
    let F : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * Δ
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let R : ℕ → ℝ := fun k => X.X (s k + Δ) ω - X.X (s k) ω
      let Z : ℕ → ℝ := fun k => R k - (Δ : ℝ) * X.c
      let H : ℕ → ℝ := fun k =>
        E (s k) * (deriv w (Y (s k)) * Z k +
          (iteratedDeriv 2 w (Y (s k)) / 2) *
            (Z k^2 - (Δ : ℝ) * X.σ^2)) +
          (Δ : ℝ) * E (s k) * X.generator w (Y (s k))
      E (ρ ω) * (w (Y (s i) +
        (X.X (ρ ω) ω - X.X (s i) ω)) - w (Y (s i))) - H i
    ∃ B : ℕ → Ω → ℝ,
      (∀ (m : ℕ) (ω : Ω), 0 ≤ B m ω) ∧
      (∀ (m : ℕ) (ω : Ω) (i : ℕ), i < m →
        (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω →
        ρ ω ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
          ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) →
          max (F m i ω) 0 ≤ B m ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun m => B m ω)
        atTop (nhds (0 : ℝ))) := by sorry
