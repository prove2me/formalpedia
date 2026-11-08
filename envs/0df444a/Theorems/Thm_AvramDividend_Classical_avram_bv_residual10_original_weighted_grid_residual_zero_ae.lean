-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_weighted_grid_residual_zero_ae
-- name    : AvramDividend.Classical.avram_bv_residual10_original_weighted_grid_residual_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:36:01.042527+00:00
-- url     : https://prove2.me/theorems/6d8e04eb-016b-40c9-a8b2-b47de8b33b58
-- title:
--   Every finite-grid weighted compensated residual vanishes for the original BV Levy path
-- statement:
--   The correction sum built from the true bounded-variation Levy residual R(t) = t drift - X(t) - the signed original negative-jump sum is almost surely zero on every physical finite grid, for arbitrary real-valued weights. Directly simplifies the second sum in B of the canonical BV-RESIDUAL10 budget and requires no Brownian-specific integral, no predictability and no mesh assumptions.
-- source:
--   AVRAM BV-RESIDUAL10 round 8, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_weighted_grid_residual_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (A : ℕ → Ω → ℕ → ℝ) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∑ i ∈ Finset.range (n + 1),
        A n ω i * (R (u n i) - R (u n (i + 1))) = 0 := by sorry
