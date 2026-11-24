-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_lop_commute
-- name    : Formalism.InvariantFactorPaths.PW.lop_commute
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:50.369693+00:00
-- url     : https://prove2.me/theorems/ea5bea9b-6d71-47b6-98cc-33e2d29eb9da
-- title:
--   PW: lop commute
-- statement:
--   The PW construction uses the lop commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L24-L31

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

theorem Formalism.InvariantFactorPaths.PW.lop_commute {A B A' B' : Module.End K W} (hA : Commute A A') (hB : Commute B B') :
    Commute (lop A B) (lop A' B') := by sorry
