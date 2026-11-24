-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_range_mem
-- name    : Formalism.InvariantFactorPaths.PW.range_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:58.993891+00:00
-- url     : https://prove2.me/theorems/127a0364-0d58-4e99-a90a-21d0ac7e0bec
-- title:
--   PW: range mem
-- statement:
--   The PW construction uses the range mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L394-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L394-L396

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

theorem Formalism.InvariantFactorPaths.PW.range_mem {a b : ι} (hab : a ≠ b) (x : W) :
    E a b x ∈ ⨆ (a : ι) (b : ι) (_ : a ≠ b), LinearMap.range (E a b) := by sorry
