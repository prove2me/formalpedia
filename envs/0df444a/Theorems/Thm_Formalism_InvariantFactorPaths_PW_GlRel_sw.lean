-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_GlRel_sw
-- name    : Formalism.InvariantFactorPaths.PW.GlRel.sw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:29.588343+00:00
-- url     : https://prove2.me/theorems/5591f7da-63f1-44b3-91ab-a3b8cdad37aa
-- title:
--   Gl Rel: sw
-- statement:
--   The Gl Rel construction uses the sw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L56-L58

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

theorem Formalism.InvariantFactorPaths.PW.GlRel.sw (h : GlRel E) (a b c d : ι) :
    E a b * E c d = E c d * E a b + ((if b = c then E a d else 0) - (if d = a then E c b else 0)) := by sorry
