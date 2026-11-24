-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_insert
-- name    : Formalism.InvariantFactorPaths.PW.Om_insert
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:58.438633+00:00
-- url     : https://prove2.me/theorems/8e247cde-4bfd-4789-b9ce-ee9f933d5b97
-- title:
--   PW: Om insert
-- statement:
--   The PW construction uses the Om insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L54-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L54-L66

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

theorem Formalism.InvariantFactorPaths.PW.Om_insert {E : ι → ι → Module.End K W} (h : GlRel E) {S : Finset ι} {z i : ι} (hz : z ∉ insert i S)
    (hi : i ∉ S) (q : ℕ) :
    Om E (insert i S) z q =
      ∑ k ∈ range (q + 1), (q.choose k : K) • ((E z i) ^ k * Om E S z (q - k) * (E i z) ^ k) := by sorry
