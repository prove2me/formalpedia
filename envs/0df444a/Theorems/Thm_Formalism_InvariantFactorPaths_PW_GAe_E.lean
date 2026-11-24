-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_E
-- name    : Formalism.InvariantFactorPaths.PW.GAe_E
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:15.801859+00:00
-- url     : https://prove2.me/theorems/d4cd97ca-b827-4c37-9283-54200de6745a
-- title:
--   PW: GAe E
-- statement:
--   The PW construction uses the GAe E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L124-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L124-L125

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}

theorem Formalism.InvariantFactorPaths.PW.GAe_E (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) (a b : Fin n) :
    (GAe p LL j e).E a b = glAct p LL j (e a) (e b) := by sorry
