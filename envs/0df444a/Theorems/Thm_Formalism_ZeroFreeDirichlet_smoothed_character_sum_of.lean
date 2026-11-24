-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_smoothed_character_sum_of
-- name    : Formalism.ZeroFreeDirichlet.smoothed_character_sum_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:44:46.786804+00:00
-- url     : https://prove2.me/theorems/8c09aef2-42e4-47f0-9fd9-023191612802
-- title:
--   Zero Free Dirichlet: smoothed character sum of
-- statement:
--   The Zero Free Dirichlet construction uses the smoothed character sum of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SmoothChiOf.lean#L9-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SmoothChiOf.lean#L9-L123

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExpGainFromZeroFreeRegion
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SmoothChiOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.smoothed_character_sum_of : SmoothChiOf := by sorry
