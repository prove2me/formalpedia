-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB232_continuous_compact_localtime_density_controls_all_interval_occupation
-- name    : AvramDividend.Classical.avram_gbB232_continuous_compact_localtime_density_controls_all_interval_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:20:41.011497+00:00
-- url     : https://prove2.me/theorems/effe4aef-ac1f-404e-927e-9832ea3e63f4
-- title:
--   Continuous compactly supported local-time representation gives uniform interval occupation bound
-- statement:
--   A stopped real-time path with an occupation-time formula represented by a continuous nonnegative compactly supported real-valued spatial local-time density has a finite uniform spatial occupation bound on every open interval. The bound is an immediate consequence of compactness and integration monotonicity; construction of a valid semimartingale local time remains separate.
-- source:
--   B227 Gaussian source local-time route: rigorously isolate deterministic compactness and integration from the hard existence and spatial continuity of a semimartingale local-time representation.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB232_continuous_compact_localtime_density_controls_all_interval_occupation
    (f : ℝ → ℝ) (n : ℕ) (ρ : ℝ)
    (ℓ : ℝ → ℝ) (R : ℝ)
    (hContinuous : Continuous ℓ)
    (hNonneg : ∀ z, 0 ≤ ℓ z)
    (hSupport : ∀ z, z ∉ Set.Icc (-R) R → ℓ z = 0)
    (hOccupation : ∀ a b : ℝ,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ f t ∈ Set.Ioo a b} =
      ∫⁻ z in Set.Ioo a b, ENNReal.ofReal (ℓ z) ∂volume) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a b : ℝ,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ f t ∈ Set.Ioo a b} ≤
      ENNReal.ofReal B * volume (Set.Ioo a b) := by sorry
