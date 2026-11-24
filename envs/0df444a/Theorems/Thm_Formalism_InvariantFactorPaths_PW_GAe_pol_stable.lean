-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_pol_stable
-- name    : Formalism.InvariantFactorPaths.PW.GAe_pol_stable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:07.34674+00:00
-- url     : https://prove2.me/theorems/1d9ec133-7074-41a7-a1ba-5dba607187fd
-- title:
--   PW: GAe pol stable
-- statement:
--   The PW construction uses the GAe pol stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L230-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L230-L232

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

theorem Formalism.InvariantFactorPaths.PW.GAe_pol_stable (LL L2 : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) :
    (GAe p LL j e).Stable (Pol p r L2) := by sorry
