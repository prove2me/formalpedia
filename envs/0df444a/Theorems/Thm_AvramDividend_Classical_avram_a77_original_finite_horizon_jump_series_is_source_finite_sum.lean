-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a77_original_finite_horizon_jump_series_is_source_finite_sum
-- name    : AvramDividend.Classical.avram_a77_original_finite_horizon_jump_series_is_source_finite_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:10:39.77664+00:00
-- url     : https://prove2.me/theorems/ce00526b-6f6f-4131-9d6f-ce4377379068
-- title:
--   Original physical finite-activity jump series agrees almost surely with finite sum over its actual jump times
-- statement:
--   For the original spectrally negative Levy process on its actual probability space under finite total negative jump activity and the original physical jump sum representative, there is almost surely a finite set of all nonzero jump times before a fixed horizon, and the original time-indexed infinite sum equals its finite sum over those times. This is the missing source-specific pathwise support-to-limit bridge for the a77 full negative mark Laplace limit. Reuses previously Proved original source finite jump support and the Proved causal finite support sum identity.
-- source:
--   Avram mission a77->8bb->5b physically marked original jump Laplace limit. Proved a88 900bfbce-d300-4373-ba5c-20fd67b5f288 and a35 83f438b9-3ced-4f77-9c2f-f96c313607f6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a77_original_finite_horizon_jump_series_is_source_finite_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0) :
    ∀ᵐ ω ∂P, ∃ S : Finset ℝ≥0,
      (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) ∧
      J ω = ∑ u ∈ S,
        (X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u) := by sorry
