-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_E_Pstep_apply
-- name    : Formalism.InvariantFactorPaths.PW.E_Pstep_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:48.406486+00:00
-- url     : https://prove2.me/theorems/a7a20e13-57f4-49ac-8e2f-1efa4f54ce35
-- title:
--   PW: E Pstep apply
-- statement:
--   The PW construction uses the E Pstep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L317-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L317-L329

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

theorem Formalism.InvariantFactorPaths.PW.E_Pstep_apply [CharZero K] (h : GlRel E) {S : Finset ι} {z j : ι} (hz : z ∉ S) (hj : j ∈ S) {u : W}
    (hS : ∀ a ∈ S, ∀ b ∈ S, E a b u = 0) (hzz : E z z u = 0) (n : ℕ) :
    E j z (Pstep E S z n u) = cc K S.card n • Om E S z n (E j z u) := by sorry
