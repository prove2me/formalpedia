-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_eq_pow
-- name    : Formalism.InvariantFactorPaths.PW.Om_eq_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:51.609998+00:00
-- url     : https://prove2.me/theorems/2f3cfc4c-12f5-41ec-9448-f622b1746f98
-- title:
--   PW: Om eq pow
-- statement:
--   The PW construction uses the Om eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L33-L40

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

theorem Formalism.InvariantFactorPaths.PW.Om_eq_pow (E : ι → ι → Module.End K W) (S : Finset ι) (z : ι) (q : ℕ) :
    Om E S z q = ((∑ i ∈ S, lop (E z i) (E i z)) ^ q) 1 := by sorry
