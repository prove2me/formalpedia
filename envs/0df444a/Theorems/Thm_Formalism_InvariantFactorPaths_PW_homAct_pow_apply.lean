-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_homAct_pow_apply
-- name    : Formalism.InvariantFactorPaths.PW.homAct_pow_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:50.057621+00:00
-- url     : https://prove2.me/theorems/5586bf50-5f3f-40be-a028-8ac8c8722fc8
-- title:
--   PW: hom Act pow apply
-- statement:
--   The PW construction uses the hom Act pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/HomRelationHolds.lean#L69-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/HomRelationHolds.lean#L69-L80

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

theorem Formalism.InvariantFactorPaths.PW.homAct_pow_apply (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W) (a b : ι) (k : ℕ)
    (φ : V →ₗ[K] W) (x : V) :
    ((homAct EV EW a b) ^ k) φ x =
      ∑ m ∈ antidiagonal k, ((k.choose m.1 : K) * (-1) ^ m.2) • ((EW a b) ^ m.1) (φ (((EV a b) ^ m.2) x)) := by sorry
