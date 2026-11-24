-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_facProd_add_single
-- name    : Formalism.InvariantFactorPaths.PW.facProd_add_single
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:36.703635+00:00
-- url     : https://prove2.me/theorems/70bff69a-4c57-4eae-beca-9fca0ed7be57
-- title:
--   PW: fac Prod add single
-- statement:
--   The PW construction uses the fac Prod add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L74-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L74-L97

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

theorem Formalism.InvariantFactorPaths.PW.facProd_add_single (m : σ →₀ ℕ) (i : σ) :
    ((m + Finsupp.single i 1).prod fun _ k => (k.factorial : ℚ_[p])) =
      ((m i : ℚ_[p]) + 1) * (m.prod fun _ k => (k.factorial : ℚ_[p])) := by sorry
