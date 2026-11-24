-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoW_le_isoC
-- name    : Formalism.InvariantFactorPaths.PW.isoW_le_isoC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:39.528537+00:00
-- url     : https://prove2.me/theorems/732eaba4-6cfc-496a-92f6-a7ada6a0f1a6
-- title:
--   PW: iso W le iso C
-- statement:
--   The PW construction uses the iso W le iso C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/PolLeISupIsoW.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/PolLeISupIsoW.lean#L49-L53

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_PolLeISupIsoW
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

theorem Formalism.InvariantFactorPaths.PW.isoW_le_isoC (LL L2 : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    IsoW (GAe p LL j (enumC Cs)) (Pol p r L2) (la ∘ enumC Cs) ≤ IsoC p LL j Cs la := by sorry
