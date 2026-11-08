-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord8_original_masked_deriv_R_grid_L1
-- name    : AvramDividend.Classical.avram_coord8_original_masked_deriv_R_grid_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:52:33.776079+00:00
-- url     : https://prove2.me/theorems/8fdce560-eff0-4f4c-885b-8e32a418a687
-- title:
--   Integrable original BV masked derivative raw-grid residual under a finite-grid coefficient bound
-- statement:
--   For the original stopped BV Lévy process and uniform finite grid, local coefficient measurability and a finite-grid uniform bound imply integrability of the original masked derivative times raw-remainder mesh differences. This removes the unnecessary all-index measurability condition from a previously proved abstract theorem, without changing the underlying stochastic process.
-- source:
--   Lean source SHA-256 fd8b78b426a704cc53dbfde0eb65db15a8c530f9d9e314b868be2b9a812978e6. Directly composes the public proved original masked derivative grid-cell measurability lemma 13fbd165 with the public proved coordinatewise bounded original BV residual integrability theorem e73d8d37.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_masked_derivative_grid_cell_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_coordinatewise_weighted_R_mesh_L1

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original masked derivative residual is integrable if its finitely many
    coefficients obey a uniform bound. -/

theorem AvramDividend.Classical.avram_coord8_original_masked_deriv_R_grid_L1
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
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (S : ℝ≥0) (huS : u n (n + 1) ≤ S)
    (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ ω i, i < n + 1 →
      |(if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Function.leftLim (fun t : ℝ≥0 =>
            x + X.X t ω - rightLimit D t ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim (fun t : ℝ≥0 =>
            x + X.X t ω - rightLimit D t ω) (u n i)) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          deriv w (Function.leftLim (fun t : ℝ≥0 =>
            x + X.X t ω - rightLimit D t ω) (u n i))
       else 0)| ≤ K) :
    Integrable (fun ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
      ∑ i ∈ Finset.range (n + 1),
        (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
         else 0) * (R (u n i) - R (u n (i + 1)))) P := by sorry
