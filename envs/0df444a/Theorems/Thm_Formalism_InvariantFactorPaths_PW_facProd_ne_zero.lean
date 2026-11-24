-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_facProd_ne_zero
-- name    : Formalism.InvariantFactorPaths.PW.facProd_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:58.314178+00:00
-- url     : https://prove2.me/theorems/c51e531c-0ebb-4bd9-9770-0f6e32c88dae
-- title:
--   PW: fac Prod ne zero
-- statement:
--   The PW construction uses the fac Prod ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L70-L72

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem Formalism.InvariantFactorPaths.PW.facProd_ne_zero (m : σ →₀ ℕ) : (m.prod fun _ k => (k.factorial : ℚ_[p])) ≠ 0 := by sorry
