-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_diag
-- name    : Formalism.InvariantFactorPaths.PW.isoC_diag
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:35:55.102071+00:00
-- url     : https://prove2.me/theorems/d4dfb631-2164-4529-85b7-aa010170855b
-- title:
--   PW: iso C diag
-- statement:
--   The PW construction uses the iso C diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L86-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L86-L96

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
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

theorem Formalism.InvariantFactorPaths.PW.isoC_diag (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (c : Fin r) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p LL j Cs la, glAct p LL j c c x ∈ IsoC p LL j Cs la := by sorry
