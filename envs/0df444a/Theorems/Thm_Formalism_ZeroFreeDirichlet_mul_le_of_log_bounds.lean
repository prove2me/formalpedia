-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_mul_le_of_log_bounds
-- name    : Formalism.ZeroFreeDirichlet.mul_le_of_log_bounds
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:42:56.841205+00:00
-- url     : https://prove2.me/theorems/64361cbc-3973-4949-9210-cabf4829c1f0
-- title:
--   Zero Free Dirichlet: mul le of log bounds
-- statement:
--   The Zero Free Dirichlet construction uses the mul le of log bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LeOfSecondDifferenceBound.lean#L127-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LeOfSecondDifferenceBound.lean#L127-L155

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LeOfSecondDifferenceBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.mul_le_of_log_bounds {y c₀ K lq : ℝ} (hy : 2 ≤ y) (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1)
    (hK : K * Real.log 2 ≤ Real.log y) (hK0 : 0 ≤ K) (hlq0 : 0 ≤ lq)
    (hlq : lq ≤ c₀ / 4 * Real.sqrt (Real.log y)) :
    K * lq ≤ 16 * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by sorry
