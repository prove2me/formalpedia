-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_Pstep_eq
-- name    : Formalism.InvariantFactorPaths.PW.Pstep_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:23.867098+00:00
-- url     : https://prove2.me/theorems/a7644cef-c42b-4113-b7b7-8d20700bac04
-- title:
--   PW: Pstep eq
-- statement:
--   The PW construction uses the Pstep eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L299-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L299-L300

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

theorem Formalism.InvariantFactorPaths.PW.Pstep_eq (S : Finset ι) (z : ι) (l : ℕ) :
    Pstep E S z l = ∑ q ∈ range (l + 1), cc K S.card q • Om E S z q := by sorry
