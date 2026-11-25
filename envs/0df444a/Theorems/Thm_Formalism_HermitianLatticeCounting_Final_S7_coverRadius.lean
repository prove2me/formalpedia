-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_Final_S7_coverRadius
-- name    : Formalism.HermitianLatticeCounting.Final.S7.coverRadius
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:06:48.929939+00:00
-- url     : https://prove2.me/theorems/f5cdd6f7-6e10-4753-a734-202e4c9b0aed
-- title:
--   S7: cover Radius
-- statement:
--   The S7 construction uses the cover Radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/HalfDeltaL1Bound.lean#L32-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/HalfDeltaL1Bound.lean#L32-L32

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDeltaL1Bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S7

theorem Formalism.HermitianLatticeCounting.Final.S7.coverRadius : Formalism.HermitianLatticeCounting.S7.CoverRadius := by sorry
