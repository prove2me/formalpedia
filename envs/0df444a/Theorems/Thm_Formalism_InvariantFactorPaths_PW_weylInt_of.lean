-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_weylInt_of
-- name    : Formalism.InvariantFactorPaths.PW.weylInt_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:47.580275+00:00
-- url     : https://prove2.me/theorems/615cb200-0ff9-44f5-8103-a9ddd67b908e
-- title:
--   PW: weyl Int of
-- statement:
--   The PW construction uses the weyl Int of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean#L150-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean#L150-L215

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
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

theorem Formalism.InvariantFactorPaths.PW.weylInt_of (hNat : InvNat) (hSchur : SchurTrace) : WeylInt := by sorry
