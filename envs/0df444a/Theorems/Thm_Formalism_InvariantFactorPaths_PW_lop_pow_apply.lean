-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_lop_pow_apply
-- name    : Formalism.InvariantFactorPaths.PW.lop_pow_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:51.791809+00:00
-- url     : https://prove2.me/theorems/688cb93b-ab9b-48fc-80f3-64832ce304a5
-- title:
--   PW: lop pow apply
-- statement:
--   The PW construction uses the lop pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L17-L22

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

theorem Formalism.InvariantFactorPaths.PW.lop_pow_apply (A B X : Module.End K W) (k : ℕ) : (lop A B ^ k) X = A ^ k * X * B ^ k := by sorry
