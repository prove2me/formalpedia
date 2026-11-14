-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB242_locally_bounded_compact_localtime_density_controls_interval_occupation
-- name    : AvramDividend.Classical.avram_gbB242_locally_bounded_compact_localtime_density_controls_interval_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:13:53.736031+00:00
-- url     : https://prove2.me/theorems/81e1151e-eea8-447d-8122-8d3e81100ca1
-- title:
--   Locally bounded compact spatial local-time density gives all-interval occupation upper bound
-- statement:
--   Assuming an exact stopped occupation representation by a nonnegative, locally bounded, compactly supported spatial density, there is a finite uniform bound for the Lebesgue occupation time of every open interval proportional to its length. The result accommodates càdlàg spatial local times typical of continuous martingale-plus-finite-variation semimartingales, with continuity unnecessary.
-- source:
--   Gaussian B227 strongest appropriate deterministic occupation-density step, spatial cadlag-friendly, follows B241 and B176.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB242_locally_bounded_compact_localtime_density_controls_interval_occupation
    (f : ℝ → ℝ) (n : ℕ) (ρ : ℝ)
    (ℓ : ℝ → ℝ) (R : ℝ)
    (hLocal : ∀ z : ℝ,
      ∃ U ∈ 𝓝 z, Bornology.IsBounded (ℓ '' U))
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
