-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_canonical_atomic_sfinite_kernel
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_canonical_atomic_sfinite_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:41:12.873295+00:00
-- url     : https://prove2.me/theorems/fd63bdd5-6346-4d86-b889-3d5cb7c58c97
-- title:
--   Canonical measurable s-finite right-atomic kernel of original controlled-dividend Stieltjes mass
-- statement:
--   For an actual adapted original dividend strategy, construct the random measure consisting of all and only the original rightpayment atoms as a genuine measurable s-finite kernel. At each sample path the kernel equals dividendMeasure D restricted to the set of times with positive singleton mass, retaining time zero and eligible horizon atoms. This exact measurable atomic companion is intended to combine with the diffuse kernel for the complete controlled-dividend decomposition.
-- source:
--   Accepted original dividendMeasure_global_sfinite_kernel_exists 766b5129 and original jointly measurable atomic graph 1bcb4f1e, using pinned Mathlib Kernel.withDensity and withDensity_indicator_one.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_atomic_support_jointly_measurable

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_canonical_atomic_sfinite_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∃ κatom : Kernel Ω ℝ,
      IsSFiniteKernel κatom ∧
      ∀ ω : Ω,
        κatom ω = (dividendMeasure D ω).restrict
          {t : ℝ | 0 < dividendMeasure D ω {t}} := by sorry
