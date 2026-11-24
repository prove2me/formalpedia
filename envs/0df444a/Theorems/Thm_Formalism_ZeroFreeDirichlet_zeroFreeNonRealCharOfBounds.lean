-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_zeroFreeNonRealCharOfBounds
-- name    : Formalism.ZeroFreeDirichlet.zeroFreeNonRealCharOfBounds
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:44:05.193211+00:00
-- url     : https://prove2.me/theorems/baaed892-d48b-463b-ac91-5e1dcba47429
-- title:
--   Zero Free Dirichlet: zero Free Non Real Char Of Bounds
-- statement:
--   The Zero Free Dirichlet construction uses the zero Free Non Real Char Of Bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/NoZeroComplexOf.lean#L30-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/NoZeroComplexOf.lean#L30-L160

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_NoZeroComplexOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
set_option maxHeartbeats 1000000

theorem Formalism.ZeroFreeDirichlet.zeroFreeNonRealCharOfBounds : NoZeroComplexOf := by sorry
