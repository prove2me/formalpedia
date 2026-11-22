-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_homAct_apply
-- name    : Formalism.InvariantFactorPaths.PW.homAct_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:09.717255+00:00
-- url     : https://prove2.me/theorems/a012d876-12c2-4246-a43c-7ea45acc5e23
-- title:
--   PW: hom Act apply
-- statement:
--   The PW construction uses the hom Act apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/HomRelationHolds.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/HomRelationHolds.lean#L11-L12

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
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
variable {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [DecidableEq ι]

theorem Formalism.InvariantFactorPaths.PW.homAct_apply (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W) (a b : ι) (φ : V →ₗ[K] W) (x : V) :
    homAct EV EW a b φ x = EW a b (φ x) - φ (EV a b x) := by sorry
