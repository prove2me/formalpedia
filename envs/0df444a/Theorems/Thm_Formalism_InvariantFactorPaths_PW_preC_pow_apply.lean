-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_preC_pow_apply
-- name    : Formalism.InvariantFactorPaths.PW.preC_pow_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:01.187911+00:00
-- url     : https://prove2.me/theorems/acfed177-268b-45ab-9511-50e1db65de69
-- title:
--   PW: pre C pow apply
-- statement:
--   The PW construction uses the pre C pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/HomRelationHolds.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/HomRelationHolds.lean#L50-L56

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

theorem Formalism.InvariantFactorPaths.PW.preC_pow_apply (Y : Module.End K V) (j : ℕ) (φ : V →ₗ[K] W) (x : V) :
    ((preC (W := W) Y) ^ j) φ x = φ ((Y ^ j) x) := by sorry
