-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_fock_wt_ne
-- name    : Formalism.InvariantFactorPaths.PW.fock_wt_ne
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:06:39.595786+00:00
-- url     : https://prove2.me/theorems/346b0ff2-0339-4afc-98ae-f894447d6630
-- title:
--   PW: fock wt ne
-- statement:
--   The PW construction uses the fock wt ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/OrthogonalIsomorphismHolds.lean#L171-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/OrthogonalIsomorphismHolds.lean#L171-L180

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
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

theorem Formalism.InvariantFactorPaths.PW.fock_wt_ne (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) {μ ν : Fin n → ℤ} (hne : μ ≠ ν)
    {x y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : (GAe p LL j e).IsWt μ x) (hy : (GAe p LL j e).IsWt ν y) :
    fock p x y = 0 := by sorry
