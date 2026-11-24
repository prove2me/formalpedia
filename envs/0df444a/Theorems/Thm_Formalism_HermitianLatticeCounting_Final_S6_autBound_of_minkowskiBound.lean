-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_Final_S6_autBound_of_minkowskiBound
-- name    : Formalism.HermitianLatticeCounting.Final.S6.autBound_of_minkowskiBound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:22.256372+00:00
-- url     : https://prove2.me/theorems/959150af-17b3-4aeb-a0a1-d0508d4b8696
-- title:
--   S6: aut Bound of minkowski Bound
-- statement:
--   The S6 construction uses the aut Bound of minkowski Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/AutBoundOfMinkowskiBound.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/AutBoundOfMinkowskiBound.lean#L34-L42

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Formalism_FlagUnipotentLattices_AutBoundOfMinkowskiBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_autBound_of_minkowskiBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S6

theorem Formalism.HermitianLatticeCounting.Final.S6.autBound_of_minkowskiBound : Formalism.HermitianLatticeCounting.S6.MinkowskiBound → Formalism.HermitianLatticeCounting.S6.AutBound := by sorry
