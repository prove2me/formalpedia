-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_homAct_postcomp
-- name    : Formalism.InvariantFactorPaths.PW.homAct_postcomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:57.423909+00:00
-- url     : https://prove2.me/theorems/8488e085-1c36-461f-a0d6-11343937d9eb
-- title:
--   PW: hom Act postcomp
-- statement:
--   The PW construction uses the hom Act postcomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/HomRelationHolds.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/HomRelationHolds.lean#L14-L19

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

theorem Formalism.InvariantFactorPaths.PW.homAct_postcomp {W' : Type} [AddCommGroup W'] [Module K W'] (EV : ι → ι → Module.End K V)
    (EW : ι → ι → Module.End K W) (EW' : ι → ι → Module.End K W') (θ : W →ₗ[K] W')
    (hθ : ∀ a b x, θ (EW a b x) = EW' a b (θ x)) (a b : ι) (φ : V →ₗ[K] W) :
    θ ∘ₗ (homAct EV EW a b φ) = homAct EV EW' a b (θ ∘ₗ φ) := by sorry
