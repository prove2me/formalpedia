-- Prove2me | Theorems.Thm_ConnesGreen_supported_test_fits_smaller_window
-- name    : ConnesGreen.supported_test_fits_smaller_window
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T21:00:44.710874+00:00
-- url     : https://prove2.me/theorems/cdbf3ddf-cbe2-49fc-88aa-7d78ef1147b7
-- title:
--   Every original compactly supported Connes test fits a strictly smaller positive window
-- statement:
--   For every positive support window $T$ and every original smooth compactly supported test $g$ with $\operatorname{tsupport}(g)\subset(-T,T)$, there exists $t$ with $0<t<T$ and $\operatorname{tsupport}(g)\subset(-t,t)$. The function is unchanged. This closes the native inner half-bound at the last good window using the existing original actor norms. It does not assert continuity or the half-bound of the support-right ordered endpoint.
-- source:
--   monocap-tech/weil, Connes/CriticalWindowBoundary.lean. SupportedTest is explicitly unfolded in the public predicate, using the original ConnesRZ.IsTest. The companion native actual-quartet cut and complete-tail identities are not asserted by this standalone export.

import Definitions.Def_ConnesRZ_weil_defs
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ Set
noncomputable section

theorem ConnesGreen.supported_test_fits_smaller_window (T : ℝ) (hT : 0 < T)
    (g : ℝ → ℂ) (hg : (IsTest g ∧ tsupport g ⊆ Ioo (-T) T)) :
    ∃ t : ℝ, 0 < t ∧ t < T ∧ (IsTest g ∧ tsupport g ⊆ Ioo (-t) t) := by sorry
