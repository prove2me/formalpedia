-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_atomic_diffuse_sfinite_kernel_full_split
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_atomic_diffuse_sfinite_kernel_full_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T22:13:59.44841+00:00
-- url     : https://prove2.me/theorems/a3706b2b-3cb2-4bde-a847-c7f32bb0d5c4
-- title:
--   Full original random Stieltjes dividend measure splits into measurable s-finite atomic and atomless kernels
-- statement:
--   For any actual adapted original dividend strategy, construct simultaneous measurable s-finite atomic and diffuse kernels whose pathwise measure sum equals the whole untruncated original dividendMeasure D, and prove every singleton has zero diffuse mass. The atomic kernel includes all original rightpayment atoms, including time zero and any horizon payment; the sum identity is measure equality, not merely equality of selected integrals.
-- source:
--   Consequence of accepted original canonical atomic kernel, canonical diffuse kernel, source deterministic no-singleton-mass lemma and jointly measurable atomic carrier, via pinned Measure.restrict_add_restrict_compl.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_canonical_atomic_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_canonical_diffuse_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_canonical_diffuse_submeasure_null_singletons
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_atomic_support_jointly_measurable

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_atomic_diffuse_sfinite_kernel_full_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∃ (κatom κdiff : Kernel Ω ℝ),
      IsSFiniteKernel κatom ∧ IsSFiniteKernel κdiff ∧
      (∀ ω : Ω, κatom ω + κdiff ω = dividendMeasure D ω) ∧
      (∀ (ω : Ω) (t : ℝ), κdiff ω {t} = 0) := by sorry
