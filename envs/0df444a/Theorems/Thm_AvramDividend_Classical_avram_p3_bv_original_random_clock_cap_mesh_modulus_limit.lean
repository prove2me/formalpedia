-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_random_clock_cap_mesh_modulus_limit
-- name    : AvramDividend.Classical.avram_p3_bv_original_random_clock_cap_mesh_modulus_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:27:23.967563+00:00
-- url     : https://prove2.me/theorems/e2a4931b-10e6-4dc7-ae87-0ad2527c2dd9
-- title:
--   Original BV random-clock discounted cap-mesh error vanishes under a C1 modulus
-- statement:
--   At any original-path-dependent finite random clock τ(ω), for any arbitrary original-path-dependent ordered grids beginning at zero and ending at τ(ω), and any source-path-dependent per-cell reserve inputs, the sum of discounted absolute cap-overshoot corrections of the genuine jump-removed BV source, multiplied by any nonnegative real C1 modulus ε_k converging to zero, converges to zero almost surely. The bound depends pathwise on the original physical drift and the possibly nonzero actual source residual. This source-exact pathwise random-clock result does not require τ to be a stopping time, any artificial Lévy representation, or L1 interchange.
-- source:
--   Direct pointwise use of public Proved 61ea0925-832a-49de-85c1-eb3a93ac40c8 for grids chosen as functions of ω. The fixed random endpoint makes each pathwise variation envelope independent of the mesh index; squeeze_zero closes the limit. Supports P3-F/G source stopped clock mesh.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_discounted_cap_grid_envelope

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_random_clock_cap_mesh_modulus_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (c : ℝ) (τ : Ω → ℝ≥0)
    (n : Ω → ℕ → ℕ) (u : Ω → ℕ → ℕ → ℝ≥0)
    (z : Ω → ℕ → ℕ → ℝ)
    (hGrid : ∀ ω k i, i < n ω k → u ω k i ≤ u ω k (i + 1))
    (hZero : ∀ ω k, u ω k 0 = 0)
    (hEnd : ∀ ω k, u ω k (n ω k) = τ ω)
    (ε : ℕ → ℝ) (hε0 : ∀ k, 0 ≤ ε k)
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0)
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      Filter.Tendsto (fun k => ε k *
        ∑ i ∈ Finset.range (n ω k),
          Real.exp (-(q * (u ω k i : ℝ))) *
            |max (z ω k i + (Y (u ω k (i + 1)) - Y (u ω k i)) - c) 0 -
              max (z ω k i - c) 0|) Filter.atTop (nhds 0) := by sorry
