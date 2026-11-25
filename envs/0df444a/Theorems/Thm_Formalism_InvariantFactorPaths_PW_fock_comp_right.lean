-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_fock_comp_right
-- name    : Formalism.InvariantFactorPaths.PW.fock_comp_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:44:54.74437+00:00
-- url     : https://prove2.me/theorems/1bc452e1-085d-4ea2-a1a1-b98f7086dd0d
-- title:
--   PW: fock comp right
-- statement:
--   The PW construction uses the fock comp right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L125-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L125-L136

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

theorem Formalism.InvariantFactorPaths.PW.fock_comp_right {n : ℕ} (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) {μ : Fin n → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : (GAe p LL j e).IsWt μ x)
    (z : MvPolynomial (Fin N × Fin r) ℚ_[p]) : fock p x z = fock p x ((GAe p LL j e).comp μ z) := by sorry
