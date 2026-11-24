-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_fock_monomial_right
-- name    : Formalism.InvariantFactorPaths.PW.fock_monomial_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:21.570428+00:00
-- url     : https://prove2.me/theorems/74838d23-cbb0-489c-ad04-75ff2be3cc39
-- title:
--   PW: fock monomial right
-- statement:
--   The PW construction uses the fock monomial right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L109-L114

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

theorem Formalism.InvariantFactorPaths.PW.fock_monomial_right (F : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) (a : ℚ_[p]) :
    fock p F (monomial m a) = F.coeff m * a * (m.prod fun _ k => (k.factorial : ℚ_[p])) := by sorry
