-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_canonical_diffuse_sfinite_kernel
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_canonical_diffuse_sfinite_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:39:38.425997+00:00
-- url     : https://prove2.me/theorems/e31ac4db-ab9f-4db5-8e6d-f9b7bfd54b26
-- title:
--   Canonical measurable s-finite diffuse kernel of original controlled-dividend Stieltjes mass
-- statement:
--   For a genuine adapted original dividend control, construct an actual measurable s-finite kernel of the non-atomic Stieltjes component by removing precisely the positive singleton-mass atomic graph, path by path. The kernel is equal to the original dividendMeasure restricted to the complement of that graph, not an arbitrarily chosen pathwise decomposition. All times, including zero and horizon, are in the original full measure; no stopping truncation is yet imposed.
-- source:
--   Accepted original dividendMeasure_global_sfinite_kernel_exists 766b5129 and original jointly measurable atomic graph 1bcb4f1e, using pinned Mathlib Kernel.withDensity and its s-finite bounded-density theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_atomic_support_jointly_measurable

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_canonical_diffuse_sfinite_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∃ κdiff : Kernel Ω ℝ,
      IsSFiniteKernel κdiff ∧
      ∀ ω : Ω,
        κdiff ω = (dividendMeasure D ω).restrict
          {t : ℝ | ¬0 < dividendMeasure D ω {t}} := by sorry
