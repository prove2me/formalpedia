-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_positive_compact_physical_Y_cell_modulus
-- name    : AvramDividend.Classical.avram_p3_f2_original_positive_compact_physical_Y_cell_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:39:33.830049+00:00
-- url     : https://prove2.me/theorems/15adf30d-3c7f-4748-b715-995760883b22
-- title:
--   Original BV jump-removed Lévy source increments uniformly small on every positive compact physical mesh
-- statement:
--   On the actual bounded-variation spectrally negative Lévy source, the already proved almost-sure uniform continuity of its true negative-jump-removed path on every strictly positive compact time interval yields one pathwise physical-time mesh modulus. Every real grid whose consecutive true times lie in that interval and have distance below delta has its actual continuous-source increments bounded by epsilon. The zero-time cell remains delegated to P3-G2.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_uniform_positive_compact
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_positive_compact_physical_Y_cell_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (a b : ℝ≥0), 0 < a →
      let Y : ℝ≥0 → ℝ := fun t =>
        X.X t ω + ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (u : ℕ → ℝ≥0) (n : ℕ),
            (∀ i, i < n →
              u i ∈ Set.Icc a b ∧ u (i + 1) ∈ Set.Icc a b) →
            (∀ i, i < n → dist (u (i + 1)) (u i) < δ) →
            ∀ i, i < n →
              |Y (u (i + 1)) - Y (u i)| < ε := by sorry
