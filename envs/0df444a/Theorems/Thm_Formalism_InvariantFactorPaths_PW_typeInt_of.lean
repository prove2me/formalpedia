-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_typeInt_of
-- name    : Formalism.InvariantFactorPaths.PW.typeInt_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:50.08246+00:00
-- url     : https://prove2.me/theorems/e22ed554-25b3-4f4f-a508-cab1b65d5947
-- title:
--   PW: type Int of
-- statement:
--   The PW construction uses the type Int of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean#L385-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean#L385-L461

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames

theorem Formalism.InvariantFactorPaths.PW.typeInt_of (hNat : InvNat) (hHom : HomInv) (hSchur : SchurTrace) : TypeInt := by sorry
