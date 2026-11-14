-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB231_continuous_compact_support_occupation_density_uniform_bound
-- name    : AvramDividend.Classical.avram_gbB231_continuous_compact_support_occupation_density_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:19:56.861062+00:00
-- url     : https://prove2.me/theorems/b082b24a-1a6e-48d8-8320-2b9f0b3379cf
-- title:
--   Continuous nonnegative compactly supported spatial occupation densities admit a finite uniform bound
-- statement:
--   A continuous nonnegative real-valued spatial occupation density vanishing outside a compact symmetric interval is bounded above by one nonnegative real constant on the whole real line. This separates the elementary compactness step from the difficult construction of a jointly valid continuous semimartingale local-time density.
-- source:
--   Gaussian B227 stochastic local-time pipeline: spatial continuity plus compact support yields finite uniform bound, reducing the stochastic core to constructing the occupation density and its spatial regularity.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB231_continuous_compact_support_occupation_density_uniform_bound
    (ℓ : ℝ → ℝ) (R : ℝ)
    (hContinuous : Continuous ℓ)
    (hNonneg : ∀ z, 0 ≤ ℓ z)
    (hSupport : ∀ z, z ∉ Set.Icc (-R) R → ℓ z = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℝ, ℓ z ≤ B := by sorry
