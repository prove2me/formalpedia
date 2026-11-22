-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_two_le_log_three_mul
-- name    : Formalism.ZeroFreeDirichlet.two_le_log_three_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:32.831279+00:00
-- url     : https://prove2.me/theorems/3e60d8db-fc93-4411-b37d-ee147cecde8a
-- title:
--   Zero Free Dirichlet: two le log three mul
-- statement:
--   The Zero Free Dirichlet construction uses the two le log three mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LDerivNearOne.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LDerivNearOne.lean#L22-L28

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

theorem Formalism.ZeroFreeDirichlet.two_le_log_three_mul (q : ℕ) (hq : 3 ≤ q) : 2 ≤ Real.log (3 * q) := by sorry
