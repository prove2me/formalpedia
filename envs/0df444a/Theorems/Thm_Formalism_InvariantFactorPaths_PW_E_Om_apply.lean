-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_E_Om_apply
-- name    : Formalism.InvariantFactorPaths.PW.E_Om_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:56.056486+00:00
-- url     : https://prove2.me/theorems/de51c3cd-7678-46d8-8ce6-b400ea9c78ca
-- title:
--   PW: E Om apply
-- statement:
--   The PW construction uses the E Om apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L302-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L302-L315

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

theorem Formalism.InvariantFactorPaths.PW.E_Om_apply (h : GlRel E) {S : Finset ι} {z j : ι} (hz : z ∉ S) (hj : j ∈ S) {u : W}
    (hS : ∀ a ∈ S, ∀ b ∈ S, E a b u = 0) (hzz : E z z u = 0) (q : ℕ) :
    E j z (Om E S z (q + 1) u) = Om E S z (q + 1) (E j z u) +
      (((q : K) + 1) * ((q : K) + 1 + S.card)) • Om E S z q (E j z u) := by sorry
