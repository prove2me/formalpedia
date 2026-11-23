-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_le_of_second_difference_bound
-- name    : Formalism.ZeroFreeDirichlet.le_of_second_difference_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:58.035864+00:00
-- url     : https://prove2.me/theorems/877d4cdd-f89b-40d9-b2bc-0bab2ba2191b
-- title:
--   Zero Free Dirichlet: le of second difference bound
-- statement:
--   The Zero Free Dirichlet construction uses the le of second difference bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LeOfSecondDifferenceBound.lean#L9-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LeOfSecondDifferenceBound.lean#L9-L125

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
set_option maxHeartbeats 800000

theorem Formalism.ZeroFreeDirichlet.le_of_second_difference_bound {y c₀ C N eY ey h : ℝ} (hy : 2 ≤ y) (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1) (hC : 0 ≤ C)
    (hh : h = Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)))
    (hey0 : 0 ≤ ey) (heY0 : 0 ≤ eY) (hey : ey ≤ h ^ 2) (heY : eY ≤ h ^ 2)
    (hmain : y * h * N ≤ (y * (1 + h) - y + 1) * ((y * (1 + h) - y) * Real.log (y * (1 + h)))
        + 2 * y ^ 2 * h ^ 2 + y * (C * (y * (1 + h)) * eY) + y * (1 + h) * (C * y * ey)) :
    N ≤ (128 / c₀ ^ 2 + 2 + 4 * C) * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by sorry
