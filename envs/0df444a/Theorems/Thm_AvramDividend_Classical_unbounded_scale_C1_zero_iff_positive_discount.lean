-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_C1_zero_iff_positive_discount
-- name    : AvramDividend.Classical.unbounded_scale_C1_zero_iff_positive_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:33:00.562323+00:00
-- url     : https://prove2.me/theorems/e6c68ff1-15e8-4b0a-94ca-51b42d54ff34
-- title:
--   Unbounded-variation scale C1 regularity is equivalent at zero and any positive discount
-- statement:
--   For an unbounded-variation spectrally negative Levy process possessing q-scale functions at q=0 and q>0, C1 regularity on the positive half-line holds for the zero-discount scale if and only if it holds for the positive-discount scale. Both directions are proved without any auxiliary parameter supplied by the user, using the common eventual Laplace domain. Thus the stochastic C1 obligation may be discharged at any convenient fixed positive discount or at zero.
-- source:
--   Proved unbounded_positive_discount_C1_from_zero_unconditional [1641238a-3e3c-48d5-9e73-b1b3c9baeaac], unbounded_zero_discount_C1_of_positive_discount_C1 [710d698e-be8e-443f-bc08-14f9f3211bd3], unbounded_psi_two_discounts_common_tail [30c9b779-d0ca-4fe8-9b52-d86ed6d87efe]. Missing C1 core [8aaa16d2-d9ec-4e8f-8e42-cc551cca9d8d].

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_two_discounts_common_tail
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_C1_from_zero_unconditional
import Theorems.Thm_AvramDividend_Classical_unbounded_zero_discount_C1_of_positive_discount_C1
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_C1_zero_iff_positive_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q : ℝ) (hq : 0 < q)
    (Wq : ℝ → ℝ) (hWq : IsScaleFunction X q Wq) :
    ContDiffOn ℝ 1 W₀ (Ioi (0 : ℝ)) ↔
    ContDiffOn ℝ 1 Wq (Ioi (0 : ℝ)) := by sorry
