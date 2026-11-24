-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_divPow_C_int
-- name    : Formalism.InvariantFactorPaths.PW.divPow_C_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:19.346796+00:00
-- url     : https://prove2.me/theorems/f2fe4bbd-2724-4941-be6e-1b2f5ffa0945
-- title:
--   PW: div Pow C int
-- statement:
--   The PW construction uses the div Pow C int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L259-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L259-L265

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

theorem Formalism.InvariantFactorPaths.PW.divPow_C_int (LL : Letters N) (j : ℕ) (c d : Fin r) (a : ℤ_[p]) (k : ℕ) :
    ((k.factorial : ℚ_[p]))⁻¹ • ((glAct p LL j c d) ^ k) (C (algebraMap ℤ_[p] ℚ_[p] a)) ∈ IntPol p (Fin N × Fin r) := by sorry
