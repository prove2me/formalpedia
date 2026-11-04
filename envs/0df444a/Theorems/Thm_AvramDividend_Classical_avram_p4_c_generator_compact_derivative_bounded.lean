-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_compact_derivative_bounded
-- name    : AvramDividend.Classical.avram_p4_c_generator_compact_derivative_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:46:53.78284+00:00
-- url     : https://prove2.me/theorems/b0d87402-e9d3-41c6-a03b-3260fb63a478
-- title:
--   Original generator C² interior derivative is uniformly bounded on every compact interior band
-- statement:
--   For any function C² on the original generator HJB interior (0,C), its ordinary derivative admits a uniform absolute bound on each compact subinterval [u,v] contained in that interior. This controls the derivative times the integrable finite-annulus mark compensation in the physical cutoff formula. It does not extend generator validity to endpoints.
-- source:
--   Original P4 source hw_smooth interior C²; pinned Mathlib ContDiffOn.continuousOn_deriv_of_isOpen and IsCompact.exists_bound_of_continuousOn

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_compact_derivative_bounded
    (w : ℝ → ℝ) (C u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hu : 0 < u) (hv : v < C) :
    ∃ M : ℝ, ∀ y ∈ Icc u v, |deriv w y| ≤ M := by sorry
