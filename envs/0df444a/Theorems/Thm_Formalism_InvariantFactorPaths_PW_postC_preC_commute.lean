-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_postC_preC_commute
-- name    : Formalism.InvariantFactorPaths.PW.postC_preC_commute
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:57.449599+00:00
-- url     : https://prove2.me/theorems/3c1f6c48-fdbc-4218-a08b-46d05b6046a8
-- title:
--   PW: post C pre C commute
-- statement:
--   The PW construction uses the post C pre C commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/HomRelationHolds.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/HomRelationHolds.lean#L58-L62

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

theorem Formalism.InvariantFactorPaths.PW.postC_preC_commute (X : Module.End K W) (Y : Module.End K V) :
    Commute (postC (V := V) X) (preC (W := W) Y) := by sorry
