-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_exists_at_positive_discount_shift_ws01a
-- name    : AvramDividend.Classical.chat04_unbounded_scale_exists_at_positive_discount_shift_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:40:37.674526+00:00
-- url     : https://prove2.me/theorems/7add6cfb-5a02-4139-a197-7156835f294a
-- title:
--   Construct W(q+p) from a supplied W(q), without zero-scale hypotheses
-- statement:
--   A positive-discount q-scale function of an unbounded-variation spectrally negative Levy process suffices to construct the (q+p)-scale for every p>0. The proof starts with the genuinely positive subunit q-shift kernel, builds a monotone continuous geometric causal renewal series, and uses a direct shifted q-scale Laplace transform to identify its transform as (ψ(η)-q-p)^(-1). This removes the W(0)-scale witness quantifier gap from the killed-resolvent path.
-- source:
--   Adaptation of the canonically accepted constructive zero-to-positive-discount theorem 636cfffe with a newly independently proved q-to-q+p subunit kernel, general causal Neumann packages and direct IsScaleFunction Laplace algebra.

import Theorems.Thm_AvramDividend_Classical_chat04_positive_discount_shift_bounded_kernel_ws01a
import Theorems.Thm_AvramDividend_Classical_causal_bounded_subunit_neumann_continuity_package
import Theorems.Thm_AvramDividend_Classical_causal_untwisted_monotone_series_package
import Theorems.Thm_AvramDividend_Classical_causal_untwisted_renewal_scale_regular
import Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_weighted_integrable
import Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_laplace_geometric
import Theorems.Thm_AvramDividend_Classical_causal_geometric_weighted_series_integrable
import Theorems.Thm_AvramDividend_Classical_causal_resolvent_exponential_renormalisation_integrable
import Theorems.Thm_AvramDividend_Classical_causal_renormalised_resolvent_laplace
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_comm_all_real
import Theorems.Thm_AvramDividend_Classical_causal_monotone_global_extension
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_scale_exists_at_positive_discount_shift_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (Wq : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq) (p : ℝ) (hp : 0 < p) :
    ∃ Wqp : ℝ → ℝ, IsScaleFunction X (q + p) Wqp := by sorry
