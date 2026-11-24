-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_comm_out
-- name    : Formalism.InvariantFactorPaths.PW.Om_comm_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:49.651802+00:00
-- url     : https://prove2.me/theorems/41047d5d-139e-4bba-8c2b-5673f6dfd1e2
-- title:
--   PW: Om comm out
-- statement:
--   The PW construction uses the Om comm out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L102-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L102-L115

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

theorem Formalism.InvariantFactorPaths.PW.Om_comm_out (h : GlRel E) {S : Finset ι} {z c : ι} (hc : c ∉ S) (hcz : z ≠ c)
    (q : ℕ) : E c c * Om E S z q = Om E S z q * E c c := by sorry
