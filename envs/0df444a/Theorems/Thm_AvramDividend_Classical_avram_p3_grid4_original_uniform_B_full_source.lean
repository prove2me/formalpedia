-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_B_full_source
-- name    : AvramDividend.Classical.avram_p3_grid4_original_uniform_B_full_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:49:45.319196+00:00
-- url     : https://prove2.me/theorems/30aeff8e-d2e2-47e2-9ff5-c017ed3167f2
-- title:
--   Original uniform stopped mesh with exact BV source, nonpositive sign and uniform coordinates
-- statement:
--   Strengthens original B witness to retain exact uniform coordinates of the physical stopped mesh, a required hypothesis for the existing genuine generator integrability and signed compensated-gap leaves 5df846f9 and 84ae946f. The B expression is literal original generator plus raw drift correction, and it is almost surely nonpositive at every mesh.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_uniform_B_full_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    ∃ (u : ℕ → ℕ → ℝ≥0) (B : ℕ → Ω → ℝ),
      (∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - δ n)) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) ∧
      (∀ n ω,
        let Z : ℕ → ℝ := fun i => Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
        B n ω =
          (∑ i ∈ Finset.range (n + 1),
            if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                0 < Z i ∧ ENNReal.ofReal (Z i) < C then
              Real.exp (-(q * (u n i : ℝ))) *
                (X.generator w (Z i) - q * w (Z i)) *
                ((u n (i + 1) : ℝ) - (u n i : ℝ))
            else 0) +
          (let J : ℝ≥0 → ℝ := fun t =>
              ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
                Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
           let R : ℝ≥0 → ℝ := fun t =>
             ((t : ℝ) * X.drift - X.X t ω) - J t
           ∑ i ∈ Finset.range (n + 1),
             (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
               Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
              else 0) * (R (u n i) - R (u n (i + 1))))) ∧
      (∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0) := by sorry
