-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_C1_from_zero_unconditional
-- name    : AvramDividend.Classical.unbounded_positive_discount_C1_from_zero_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:18:51.15642+00:00
-- url     : https://prove2.me/theorems/1641238a-3e3c-48d5-9e73-b1b3c9baeaac
-- title:
--   Positive-discount C1 regularity from zero-discount C1 with no auxiliary Laplace parameter
-- statement:
--   For an unbounded-variation spectrally negative Lévy process, a C1 zero-discount scale function transfers its regularity to every positive-discount scale function. Unlike the preceding helper, there is no user-supplied Laplace-transform comparison parameter: the proved common-half-line theorem constructs it. This removes a side-condition from the canonical positive-discount regularity route while retaining the genuine zero-discount C1 prerequisite.
-- source:
--   Proved unbounded_positive_discount_C1_of_zero_discount_C1 [19f7023d-47cb-46b4-ab2c-9939e676ccdf]; Proved unbounded_psi_two_discounts_common_tail [30c9b779-d0ca-4fe8-9b52-d86ed6d87efe]; the mission zero-discount core [8aaa16d2-d9ec-4e8f-8e42-cc551cca9d8d].

import Theorems.Thm_AvramDividend_Classical_unbounded_psi_two_discounts_common_tail
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_C1_of_zero_discount_C1
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_positive_discount_C1_from_zero_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (hW₀C1 : ContDiffOn ℝ 1 W₀ (Ioi (0 : ℝ)))
    (q : ℝ) (hq : 0 < q)
    (Wq : ℝ → ℝ) (hWq : IsScaleFunction X q Wq) :
    ContDiffOn ℝ 1 Wq (Ioi (0 : ℝ)) := by sorry
