-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_normInvEntryLeMinor
-- name    : Formalism.HermitianLatticeCounting.P.normInvEntryLeMinor
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:40:01.387487+00:00
-- url     : https://prove2.me/theorems/9a1f9974-43b5-4425-8b6f-3205d49794eb
-- title:
--   P: norm Inv Entry Le Minor
-- statement:
--   The P construction uses the norm Inv Entry Le Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L1299-L1304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeSumBounds.lean#L1299-L1304

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.normInvEntryLeMinor : InverseEntryMinor := by sorry
