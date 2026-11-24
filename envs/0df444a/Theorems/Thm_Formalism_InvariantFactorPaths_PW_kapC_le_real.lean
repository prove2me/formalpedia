-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_kapC_le_real
-- name    : Formalism.InvariantFactorPaths.PW.kapC_le_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:42.946258+00:00
-- url     : https://prove2.me/theorems/f536fd9d-6b2a-4b97-9030-0d28264a8983
-- title:
--   PW: kap C le real
-- statement:
--   The PW construction uses the kap C le real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/Discharge.lean#L52-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/Discharge.lean#L52-L97

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_Discharge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M Formalism.GM

theorem Formalism.InvariantFactorPaths.PW.kapC_le_real (p : ℕ) [Fact p.Prime] (r d a : ℕ) (h : d + r ≤ p ^ 2 * (8 * a + r) ^ 2) :
    (kapC p r d : ℝ) ≤ (r : ℝ) ^ 2 * lgV2 p a r := by sorry
