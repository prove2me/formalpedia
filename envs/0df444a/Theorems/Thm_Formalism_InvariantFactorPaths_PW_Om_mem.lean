-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_mem
-- name    : Formalism.InvariantFactorPaths.PW.Om_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:14.200819+00:00
-- url     : https://prove2.me/theorems/65c8387f-ef52-4373-a866-61fcf7b70e9c
-- title:
--   PW: Om mem
-- statement:
--   The PW construction uses the Om mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L239-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L239-L246

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

theorem Formalism.InvariantFactorPaths.PW.Om_mem {NN : Submodule K W} (hN : ∀ a b, ∀ x ∈ NN, E a b x ∈ NN) (S : Finset ι) (z : ι) (q : ℕ) :
    ∀ x ∈ NN, Om E S z q x ∈ NN := by sorry
