-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_Cj_E
-- name    : Formalism.InvariantFactorPaths.PW.Cj_E
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:43.2518+00:00
-- url     : https://prove2.me/theorems/35f3910b-1040-4f4a-8eb1-282959b32dd9
-- title:
--   PW: Cj E
-- statement:
--   The PW construction uses the Cj E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L138-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L138-L166

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

theorem Formalism.InvariantFactorPaths.PW.Cj_E (h : GlRel E) {S : Finset ι} {z j k : ι} (hz : z ∉ S) (hj : j ∈ S) (hk : k ∈ S) :
    Cj E S z j * E k z = E k z * Cj E S z j + (2 : K) • (E k z * E j z) := by sorry
