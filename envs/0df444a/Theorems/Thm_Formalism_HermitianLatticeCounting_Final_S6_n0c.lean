-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_Final_S6_n0c
-- name    : Formalism.HermitianLatticeCounting.Final.S6.n0c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:38:03.488542+00:00
-- url     : https://prove2.me/theorems/f10947b0-df44-4207-9a50-042fefea4bf0
-- title:
--   S6: n0c
-- statement:
--   The S6 construction uses the n0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/AutBoundOfMinkowskiBound.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/AutBoundOfMinkowskiBound.lean#L11-L14

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Formalism_FlagUnipotentLattices_AutBoundOfMinkowskiBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S6

theorem Formalism.HermitianLatticeCounting.Final.S6.n0c : Formalism.HermitianLatticeCounting.S6.MemOfOrthogonalAnisotropic := by sorry
