-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b27_original_all_size2_jump_source_count
-- name    : AvramDividend.Classical.avram_b27_original_all_size2_jump_source_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:45:39.617521+00:00
-- url     : https://prove2.me/theorems/613ea4ec-89e8-4600-aeb0-d1edd03bc045
-- title:
--   For any original Lévy path with only size-two negative jumps, the exact signed large-mark source is minus twice its finite jump count
-- statement:
--   For an original spectrally negative Lévy process path and a finite physical horizon, suppose every nonzero positive-time jump has actual size precisely -2. The existing Proved finite-support theorem for marks <=-1 supplies a finite set of exactly the nonzero physical jump times; its equivalence is proved using the size-two hypothesis. The existing Proved original raw-large-jump count-to-finite-sum identity then yields the exact signed intrinsic source -2 times the finite jump count, including all actual physical jumps and without introducing a compensated surrogate. A concrete Poisson counting process can subsequently be identified with F.card.
-- source:
--   Prove2Me Proved e45c2694 finite support of original large jump times, 48bb5af6 original large jump source equals finite physical mark sum; B25/B27 Brownian-minus-two-Poisson obstruction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_tsum_finite_support
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_largejump_raw_source_equals_physical_finite_mark_sum
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_b27_original_all_size2_jump_source_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0)
    (hSize : ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = -2)) :
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
        -2 * (F.card : ℝ) := by sorry
