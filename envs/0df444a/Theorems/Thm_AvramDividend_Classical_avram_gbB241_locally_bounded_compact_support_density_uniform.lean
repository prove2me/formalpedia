-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB241_locally_bounded_compact_support_density_uniform
-- name    : AvramDividend.Classical.avram_gbB241_locally_bounded_compact_support_density_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:13:03.301208+00:00
-- url     : https://prove2.me/theorems/573a4646-4e85-4ed6-9817-1ccd5dd9365d
-- title:
--   Locally bounded compactly supported spatial occupation density admits a uniform finite bound
-- statement:
--   Any nonnegative real spatial occupation density that is locally bounded at every spatial level and vanishes outside a compact symmetric interval admits one global finite nonnegative bound. The lemma applies to cadlag rather than necessarily continuous local-time fields and is therefore a more appropriate bridge for continuous martingale-plus-finite-variation semimartingales.
-- source:
--   Avram Gaussian B227 original semimartingale Tanaka/local-time pipeline: replace over-strong continuous-spatial-density B231 premise by realistic locally bounded cadlag-spatial-density premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB241_locally_bounded_compact_support_density_uniform
    (ℓ : ℝ → ℝ) (R : ℝ)
    (hLocal : ∀ z : ℝ,
      ∃ U ∈ 𝓝 z, Bornology.IsBounded (ℓ '' U))
    (hNonneg : ∀ z : ℝ, 0 ≤ ℓ z)
    (hSupport : ∀ z, z ∉ Set.Icc (-R) R → ℓ z = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℝ, ℓ z ≤ B := by sorry
