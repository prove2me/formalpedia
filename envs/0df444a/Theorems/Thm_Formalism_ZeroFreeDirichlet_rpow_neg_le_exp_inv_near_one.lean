-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_rpow_neg_le_exp_inv_near_one
-- name    : Formalism.ZeroFreeDirichlet.rpow_neg_le_exp_inv_near_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:44:27.318774+00:00
-- url     : https://prove2.me/theorems/a74fb49d-1914-4fc0-bb3c-f673cba7b788
-- title:
--   Zero Free Dirichlet: rpow neg le exp inv near one
-- statement:
--   The Zero Free Dirichlet construction uses the rpow neg le exp inv near one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LDerivNearOne.lean#L50-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LDerivNearOne.lean#L50-L61

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.rpow_neg_le_exp_inv_near_one (q : ℕ) (hq : 3 ≤ q) (x : ℝ) (hx : 1 ≤ x) (hxq : x ≤ q) (r : ℝ)
    (hr : 1 - 3 / (2 * Real.log (3 * q)) ≤ r) :
    x ^ (-r) ≤ Real.exp (3 / 2) * x⁻¹ := by sorry
