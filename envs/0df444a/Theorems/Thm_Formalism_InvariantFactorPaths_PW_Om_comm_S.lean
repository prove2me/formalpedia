-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_comm_S
-- name    : Formalism.InvariantFactorPaths.PW.Om_comm_S
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:16.548462+00:00
-- url     : https://prove2.me/theorems/86d5e891-3ad7-4d4d-8b12-4e8f79a90616
-- title:
--   PW: Om comm S
-- statement:
--   The PW construction uses the Om comm S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L60-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L60-L84

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

theorem Formalism.InvariantFactorPaths.PW.Om_comm_S (h : GlRel E) {S : Finset ι} {z : ι} (hz : z ∉ S) {a b : ι} (ha : a ∈ S) (hb : b ∈ S)
    (q : ℕ) : E a b * Om E S z q = Om E S z q * E a b := by sorry
