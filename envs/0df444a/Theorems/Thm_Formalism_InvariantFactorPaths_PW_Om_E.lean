-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_E
-- name    : Formalism.InvariantFactorPaths.PW.Om_E
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:56.905657+00:00
-- url     : https://prove2.me/theorems/0e29309b-817c-4073-bacc-ebf0d2ac10de
-- title:
--   PW: Om E
-- statement:
--   The PW construction uses the Om E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L190-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L190-L221

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

theorem Formalism.InvariantFactorPaths.PW.Om_E (h : GlRel E) {S : Finset ι} {z j : ι} (hz : z ∉ S) (hj : j ∈ S) (q : ℕ) :
    E j z * Om E S z (q + 1) = Om E S z (q + 1) * E j z +
      ((q : K) + 1) • (Om E S z q * (Cj E S z j + (q : K) • E j z)) := by sorry
