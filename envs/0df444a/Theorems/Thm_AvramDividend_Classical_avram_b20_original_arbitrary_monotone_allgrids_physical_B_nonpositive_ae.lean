-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b20_original_arbitrary_monotone_allgrids_physical_B_nonpositive_ae
-- name    : AvramDividend.Classical.avram_b20_original_arbitrary_monotone_allgrids_physical_B_nonpositive_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:22:31.187201+00:00
-- url     : https://prove2.me/theorems/cfb98db5-f75e-4013-8a3f-fc0feeb8b1cb
-- title:
--   All physical BV signed HJB grid B terms are nonpositive on one a.s. event for arbitrary monotone meshes
-- statement:
--   For every deterministic family of monotone grids of arbitrary shape, the original physical bounded-variation Lévy generator sum plus its exact drift-minus-negative-jump residual R is nonpositive at all rows simultaneously on a single probability-one event. Uniform grids and a priori integrability of B are not required. This directly establishes the universally usable B-sign half of the original residual9 stochastic source.
-- source:
--   Source-exact countable intersection of Proved original finite-grid physical B HJB sign theorem 81d78723, one row at a time. Uses no additional hypotheses, process surrogates, or circular reduction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_b20_original_arbitrary_monotone_allgrids_physical_B_nonpositive_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) :
    ∀ᵐ ω ∂P, ∀ n,
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
         else 0) * (R (u n i) - R (u n (i + 1)))) ≤ 0 := by sorry
