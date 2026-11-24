-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_Pstep_sub_mem
-- name    : Formalism.InvariantFactorPaths.PW.Pstep_sub_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:59.918142+00:00
-- url     : https://prove2.me/theorems/bf039280-4c5b-40c5-9cca-98435abedfc9
-- title:
--   PW: Pstep sub mem
-- statement:
--   The PW construction uses the Pstep sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L398-L404
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L398-L404

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

theorem Formalism.InvariantFactorPaths.PW.Pstep_sub_mem [CharZero K] {S : Finset ι} {z : ι} (hz : z ∉ S) (l : ℕ) (u : W) :
    Pstep E S z l u - u ∈ ⨆ (a : ι) (b : ι) (_ : a ≠ b), LinearMap.range (E a b) := by sorry
