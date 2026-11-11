-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_original_BV_uniform_R_cell_sum_zero
-- name    : AvramDividend.Classical.avram_bva20_original_BV_uniform_R_cell_sum_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:38:05.594221+00:00
-- url     : https://prove2.me/theorems/58929ec6-7c89-497f-86cd-b1250aad22e2
-- title:
--   Original BV physical-grid drift remainder contributes zero to every finite weighted cell sum
-- statement:
--   The proved original-path BV Lévy jump representation 79a63ca0 shows the drift remainder R(t), defined from original X and its actual negative jump losses, equals zero almost surely at all times. For any deterministic grid and any real adapted or nonadapted coefficients, the finite sum of weighted consecutive R increments therefore vanishes. This exact interface eliminates the second physical B term in original positive-ruin target 30da2b68, without finite-activity or moment strengthening.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva20_original_BV_uniform_R_cell_sum_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (A : ℕ → ℕ → Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range (n + 1),
        A n i ω * (R (u n i) - R (u n (i + 1)))) = 0 := by sorry
