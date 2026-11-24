-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_nFCaseA_of_lastVectorNotMemSup
-- name    : Formalism.HermitianLatticeCounting.P.nFCaseA_of_lastVectorNotMemSup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:22.518488+00:00
-- url     : https://prove2.me/theorems/caef62ec-8410-4b6f-bebe-9260b59909c4
-- title:
--   P: n FCase A of last Vector Not Mem Sup
-- statement:
--   The P construction uses the n FCase A of last Vector Not Mem Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L564-L637
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L564-L637

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.nFCaseA_of_lastVectorNotMemSup (hStep : Formalism.HermitianLatticeCounting.S6.NFStep) (hN0 : Formalism.HermitianLatticeCounting.S6.LastVectorNotMemSup) : Formalism.HermitianLatticeCounting.S6.NFCaseA := by sorry
