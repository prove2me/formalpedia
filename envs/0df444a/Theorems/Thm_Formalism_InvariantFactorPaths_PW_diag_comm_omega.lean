-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_diag_comm_omega
-- name    : Formalism.InvariantFactorPaths.PW.diag_comm_omega
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:55.743299+00:00
-- url     : https://prove2.me/theorems/993126ba-e9d0-4276-9e9c-acc9f27b5154
-- title:
--   PW: diag comm omega
-- statement:
--   The PW construction uses the diag comm omega property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L86-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L86-L97

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
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
variable {E : ι → ι → Module.End K W}

theorem Formalism.InvariantFactorPaths.PW.diag_comm_omega (h : GlRel E) {S : Finset ι} {z : ι} (hz : z ∉ S)
    (q : ℕ) : E z z * Om E S z q = Om E S z q * E z z := by sorry
