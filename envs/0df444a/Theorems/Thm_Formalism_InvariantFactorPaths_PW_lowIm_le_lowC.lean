-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_lowIm_le_lowC
-- name    : Formalism.InvariantFactorPaths.PW.lowIm_le_lowC
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:37:14.398908+00:00
-- url     : https://prove2.me/theorems/7b774db9-31a9-43ea-b13d-1c46eb03339d
-- title:
--   PW: low Im le low C
-- statement:
--   The PW construction uses the low Im le low C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L108-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L108-L114

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

theorem Formalism.InvariantFactorPaths.PW.lowIm_le_lowC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) :
    lowIm (GAe p LL j (enumC Cs)) ≤ lowC p LL j Cs := by sorry
