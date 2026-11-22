-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_der3
-- name    : Formalism.InvariantFactorPaths.PW.der3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:38:46.62541+00:00
-- url     : https://prove2.me/theorems/6a50b20b-adc8-4b3b-aeb6-f98179a49fac
-- title:
--   PW: der3
-- statement:
--   The PW construction uses the der3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L40-L47

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {R : Type} [Ring R]

theorem Formalism.InvariantFactorPaths.PW.der3 (x f o e f' o' e' : R) (hf : x * f = f * x + f') (ho : x * o = o * x + o')
    (he : x * e = e * x + e') :
    x * (f * o * e) = (f * o * e) * x + (f' * o * e + f * o' * e + f * o * e') := by sorry
