-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_halfline_support_of_measure_convolution
-- name    : AvramDividend.Classical.nonnegative_halfline_support_of_measure_convolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T18:46:37.835989+00:00
-- url     : https://prove2.me/theorems/e48c6630-4667-4a0a-b09c-295da38e4fb4
-- title:
--   Convolution preserves support on the nonnegative half-line
-- statement:
--   Convolution of two s-finite measures supported on the nonnegative real half-line stays supported there. This factors the original accepted positive_finite_supported_geometric_renewal_uniform proof and enables a compact strengthened finite geometric renewal package retaining positive-axis absolute continuity. Combined with geometric_convolution_renewal_positive_part_ac, it advances the exact corrected Esscher renewal density theorem 9be5ada9 toward cstar_lt_top.
-- source:
--   Extracted verbatim from the canonically Proved positive_finite_supported_geometric_renewal_uniform proof's inner hconvSupport argument.

import Theorems.Thm_AvramDividend_Classical_positive_finite_supported_geometric_renewal_uniform
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.nonnegative_halfline_support_of_measure_convolution
    (κ ν : Measure ℝ) [SFinite κ] [SFinite ν]
    (hκ : κ (Iio (0 : ℝ)) = 0)
    (hν : ν (Iio (0 : ℝ)) = 0) :
    (Measure.conv κ ν) (Iio (0 : ℝ)) = 0 := by sorry
