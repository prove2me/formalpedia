-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_log_deriv_in_zero_free_region
-- name    : Formalism.ZeroFreeDirichlet.log_deriv_in_zero_free_region
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:42:55.705663+00:00
-- url     : https://prove2.me/theorems/badc5c68-a378-42fb-acb9-5ba5f52d57f0
-- title:
--   Zero Free Dirichlet: log deriv in zero free region
-- statement:
--   The Zero Free Dirichlet construction uses the log deriv in zero free region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LogDerivRegionChiOf.lean#L10-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LogDerivRegionChiOf.lean#L10-L79

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLemmaLfunctionZeros
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogDerivSubExceptionalZeros
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogDerivRegionChiOf
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

theorem Formalism.ZeroFreeDirichlet.log_deriv_in_zero_free_region : LogDerivRegionChiOf := by sorry
