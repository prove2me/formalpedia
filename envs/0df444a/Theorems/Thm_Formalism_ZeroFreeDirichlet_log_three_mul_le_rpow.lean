-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_log_three_mul_le_rpow
-- name    : Formalism.ZeroFreeDirichlet.log_three_mul_le_rpow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:43:27.430191+00:00
-- url     : https://prove2.me/theorems/72098121-9612-4cec-82af-a902bed06318
-- title:
--   Zero Free Dirichlet: log three mul le rpow
-- statement:
--   The Zero Free Dirichlet construction uses the log three mul le rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelBoundSameCharacter.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelBoundSameCharacter.lean#L9-L15

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelBoundSameCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.log_three_mul_le_rpow {N ε : ℝ} (hN : 0 ≤ N) (hε : 0 < ε) :
    Real.log (3 * N) ≤ 2 * (3 : ℝ) ^ (ε / 2) / ε * N ^ (ε / 2) := by sorry
