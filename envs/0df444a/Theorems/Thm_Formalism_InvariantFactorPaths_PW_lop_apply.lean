-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_lop_apply
-- name    : Formalism.InvariantFactorPaths.PW.lop_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:27.026378+00:00
-- url     : https://prove2.me/theorems/f691302a-5ac1-4cb3-80de-6ef8ffd0efa6
-- title:
--   PW: lop apply
-- statement:
--   The PW construction uses the lop apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L14-L15

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
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

theorem Formalism.InvariantFactorPaths.PW.lop_apply (A B X : Module.End K W) : lop A B X = A * X * B := by sorry
