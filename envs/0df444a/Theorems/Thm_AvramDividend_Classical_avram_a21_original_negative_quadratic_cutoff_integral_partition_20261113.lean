-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_negative_quadratic_cutoff_integral_partition_20261113
-- name    : AvramDividend.Classical.avram_a21_original_negative_quadratic_cutoff_integral_partition_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:29:52.459078+00:00
-- url     : https://prove2.me/theorems/ca95021a-eab2-44fd-aff8-7cb8e16979c1
-- title:
--   Exact cutoff partition of original finite-activity negative Levy quadratic mass
-- statement:
--   Under finite negative Lévy activity, the original negative small-jump squared-mark integral on (-1,0) is exactly the sum of the retained original strip (-1,-1/(n+1)] and omitted near-zero tail (-1/(n+1),0), including any atom at the cutoff in the retained strip.
-- source:
--   Pinned Mathlib setIntegral_union and Set.Ioc_union_Ioo_eq_Ioo, physical cutoff endpoint arithmetic and finite negative Lévy mass. Supports source Gaussian finite-cutoff variance 74450e6a without using disproved retained-versus-omitted variance d73cacfa.

import Mathlib
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_negative_quadratic_cutoff_integral_partition_20261113
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) ≠ ⊤) (n : ℕ) :
    (∫ z in Ioo (-1 : ℝ) 0, z ^ 2 ∂ν) =
      (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ^ 2 ∂ν) +
      (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂ν) := by sorry
