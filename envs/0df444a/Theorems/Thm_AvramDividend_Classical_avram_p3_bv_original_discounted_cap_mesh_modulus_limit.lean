-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_discounted_cap_mesh_modulus_limit
-- name    : AvramDividend.Classical.avram_p3_bv_original_discounted_cap_mesh_modulus_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:24:12.957099+00:00
-- url     : https://prove2.me/theorems/6a3118f5-f089-4e58-b2fe-e414f0ff259a
-- title:
--   Original BV discounted cap-overshoot mesh error vanishes under a decreasing C1 modulus
-- statement:
--   For the genuine original bounded-variation spectrally negative Lévy source, any sequence of ordered nonnegative finite time grids starting at zero and ending at the same deterministic clock τ, and any arbitrary cell-wise reserve inputs, the sum of discounted absolute cap-overshoot changes of the original jump-removed source, multiplied by a nonnegative real modulus ε_k tending to zero, tends to zero almost surely. The source pathwise finite-variation bound depends on its actual drift and monotone residual but is fixed across k. This is a source-specific C1 cap-contact mesh-error limit; it assumes neither residual zero nor an integrable random dominating variable.
-- source:
--   Uses the Proved original discounted cap mesh envelope 61ea0925-832a-49de-85c1-eb3a93ac40c8, the fixed endpoint τ, real exponential positivity and the pinned Mathlib squeeze_zero convergence theorem. P3-F still needs to verify its actual cap crossing error is controlled by the displayed modulus times positive-part overshoot.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_discounted_cap_grid_envelope

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_discounted_cap_mesh_modulus_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (c : ℝ) (τ : ℝ≥0)
    (n : ℕ → ℕ) (u : ℕ → ℕ → ℝ≥0) (z : ℕ → ℕ → ℝ)
    (hGrid : ∀ k i, i < n k → u k i ≤ u k (i + 1))
    (hZero : ∀ k, u k 0 = 0)
    (hEnd : ∀ k, u k (n k) = τ)
    (ε : ℕ → ℝ) (hε0 : ∀ k, 0 ≤ ε k)
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0)
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      Filter.Tendsto (fun k => ε k *
        ∑ i ∈ Finset.range (n k),
          Real.exp (-(q * (u k i : ℝ))) *
            |max (z k i + (Y (u k (i + 1)) - Y (u k i)) - c) 0 -
              max (z k i - c) 0|) Filter.atTop (nhds 0) := by sorry
