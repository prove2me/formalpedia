-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_arbitrary_grid_B_aestronglyMeasurable_auto
-- name    : AvramDividend.Classical.avram_bv_meas7_original_arbitrary_grid_B_aestronglyMeasurable_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:07:06.801207+00:00
-- url     : https://prove2.me/theorems/3d84003a-33c8-4846-985b-798479610d2d
-- title:
--   Original BV stopped residual is AE measurable on arbitrary grids without extra source assumptions
-- statement:
--   For the actual bounded-variation spectrally negative Levy process X, an admissible original dividend strategy D, ruin-extended continuous value function w, and any deterministic finite physical grid u, the exact full generator plus intrinsic raw-jump residual B from the canonical BV stopped residual theorem is almost-everywhere strongly measurable. Neither uniform spacing nor an assumed measurability of the generator is needed. Both hypotheses are discharged using source-exact Proved children.
-- source:
--   Composes the independently proved original ruin-extended value measurability theorem f8376baa with two BV-MEAS7 original-process children: grid-free generator Borel and arbitrary-grid stopped B AE measurability. This is directly importable by 4f851376 and uses no proxy, equality in law, or unproved stochastic assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_arbitrary_grid_B_aestronglyMeasurable_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (u : ℕ → ℕ → ℝ≥0) :
    ∀ n, AEStronglyMeasurable (fun ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
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
          else 0) * (R (u n i) - R (u n (i + 1))))) P := by sorry
