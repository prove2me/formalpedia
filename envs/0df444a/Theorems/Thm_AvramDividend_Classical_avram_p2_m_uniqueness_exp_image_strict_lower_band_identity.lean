-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_exp_image_strict_lower_band_identity
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_exp_image_strict_lower_band_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:20:36.43085+00:00
-- url     : https://prove2.me/theorems/ecf4a488-9348-4525-8a66-dd7b549362a2
-- title:
--   Strict-lower-band exponential image identity for arbitrary real measures
-- statement:
--   For an arbitrary Borel real measure σ and cutoffs a,b, the σ.map exp mass on (exp(a),exp(b)] exactly equals the original σ mass on (a,b]. Strictness at the lower endpoint is preserved, which is essential for the original separated negative-mark bands and does not assume any jump-count intensity.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_p2_m_uniqueness_exp_image_strict_lower_band_identity (σ : Measure ℝ) (a b : ℝ) : (σ.map Real.exp) (Ioc (Real.exp a) (Real.exp b)) = σ (Ioc a b) := by sorry
