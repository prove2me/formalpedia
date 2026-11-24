-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_InvOp_comm_out
-- name    : Formalism.InvariantFactorPaths.PW.InvOp_comm_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:48.735342+00:00
-- url     : https://prove2.me/theorems/8f2003fb-80f3-4d81-be33-d19a25860ce6
-- title:
--   PW: Inv Op comm out
-- statement:
--   The PW construction uses the Inv Op comm out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L227-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L227-L237

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

theorem Formalism.InvariantFactorPaths.PW.InvOp_comm_out (h : GlRel E) (l : ℕ) (c : ι) (L : List ι) (hc : c ∉ L) :
    E c c * InvOp E l L = InvOp E l L * E c c := by sorry
