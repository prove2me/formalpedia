-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_map_of_comm
-- name    : Formalism.InvariantFactorPaths.PW.isoC_map_of_comm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:14.654217+00:00
-- url     : https://prove2.me/theorems/acb2cbcf-f0d9-45db-87d8-53187e8ff253
-- title:
--   PW: iso C map of comm
-- statement:
--   The PW construction uses the iso C map of comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CommProjectionHolds.lean#L70-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CommProjectionHolds.lean#L70-L83

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.PW.isoC_map_of_comm (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x)) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p LL j Cs la, A x ∈ IsoC p LL j Cs la := by sorry
