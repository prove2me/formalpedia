-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_original_uniform_grid_exists_exact_B_nonpositive_and_true_prepayment
-- name    : AvramDividend.Classical.avram_bvb_original_uniform_grid_exists_exact_B_nonpositive_and_true_prepayment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:03:29.119682+00:00
-- url     : https://prove2.me/theorems/de7aafdf-a293-4438-b2e2-1dea314040b2
-- title:
--   Witness the actual original BV physical residual B and prove both target almost-sure grid premises simultaneously
-- statement:
--   For a Standing BV spectrally negative Lévy process with original HJB supersolution and original uniform monotone physical grid, there is a canonical actual generator-plus-drift-residual field B with precisely the target hB formula, nonpositive a.e. on all grid rows, while the genuine prepayment reserve equals the risk process a.e. on every positive endpoint.
-- source:
--   Construct the canonical exact original B from the target hB definition; use the Proved joint original HJB B nonpositivity and prepayment equality to discharge the two almost-sure target premises simultaneously.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_strict_uniform_grid_HJB_B_nonpos_and_prepayment_ae
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_original_uniform_grid_exists_exact_B_nonpositive_and_true_prepayment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hMono : ∀ n i, u n i ≤ u n (i + 1))
    (hUniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∃ B : ℕ → Ω → ℝ,
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
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t =>
           ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range (n + 1),
           (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
           else 0) * (R (u n i) - R (u n (i + 1))))) ∧
    (∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0) ∧
    (∀ᵐ ω ∂P, ∀ n i,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω) := by sorry
