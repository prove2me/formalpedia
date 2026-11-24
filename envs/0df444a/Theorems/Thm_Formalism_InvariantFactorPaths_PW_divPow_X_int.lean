-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_divPow_X_int
-- name    : Formalism.InvariantFactorPaths.PW.divPow_X_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:11.570862+00:00
-- url     : https://prove2.me/theorems/7ed4ac2e-90e4-40fd-85bb-36f292630611
-- title:
--   PW: div Pow X int
-- statement:
--   The PW construction uses the div Pow X int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L250-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L250-L257

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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.PW.divPow_X_int (LL : Letters N) (j : ℕ) (c d : Fin r) (hcd : c ≠ d) (v : Fin N × Fin r) (k : ℕ) :
    ((k.factorial : ℚ_[p]))⁻¹ • ((glAct p LL j c d) ^ k) (X v) ∈ IntPol p (Fin N × Fin r) := by sorry
