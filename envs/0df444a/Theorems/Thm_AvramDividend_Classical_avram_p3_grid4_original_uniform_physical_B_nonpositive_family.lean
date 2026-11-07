-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_physical_B_nonpositive_family
-- name    : AvramDividend.Classical.avram_p3_grid4_original_uniform_physical_B_nonpositive_family
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:52:16.640605+00:00
-- url     : https://prove2.me/theorems/c8ca588a-2702-4382-b4b5-1800b61fbfc8
-- title:
--   Original uniform physical stopped grids have nonpositive full B source almost surely
-- statement:
--   Combine the accepted explicit uniform physical grid with the accepted literal original BV HJB and raw drift-residual correction sign, obtaining one grid witness whose full B sum is almost surely nonpositive at every index. This solves the geometry and B-sign clauses jointly for the original c1e2f021 physical source witness without introducing alternative processes or conditioning away ruin.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_uniform_physical_B_nonpositive_family
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
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - δ n)) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n, ∀ᵐ ω ∂P,
        let Z : ℕ → ℝ := fun i => Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
        let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) - J t
        (∑ i ∈ Finset.range (n + 1),
          if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
              0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) *
              ((u n (i + 1) : ℝ) - (u n i : ℝ))
          else 0) +
        (∑ i ∈ Finset.range (n + 1),
          (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
              0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
           else 0) * (R (u n i) - R (u n (i + 1)))) ≤ 0) := by sorry
