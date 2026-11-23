-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_Pstep_mem
-- name    : Formalism.InvariantFactorPaths.PW.Pstep_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:20.359583+00:00
-- url     : https://prove2.me/theorems/00e40f48-505d-4f78-a22b-e0d10303d1e9
-- title:
--   PW: Pstep mem
-- statement:
--   The PW construction uses the Pstep mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L248-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L248-L252

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

theorem Formalism.InvariantFactorPaths.PW.Pstep_mem {NN : Submodule K W} (hN : ∀ a b, ∀ x ∈ NN, E a b x ∈ NN) (S : Finset ι) (z : ι) (l : ℕ) :
    ∀ x ∈ NN, Pstep E S z l x ∈ NN := by sorry
