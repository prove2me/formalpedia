-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_gSall_le_perpV
-- name    : Formalism.InvariantFactorPaths.PW.gSall_le_perpV
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:08:19.056974+00:00
-- url     : https://prove2.me/theorems/52a93baf-fdb3-48a0-aba3-37453f423a8a
-- title:
--   PW: g Sall le perp V
-- statement:
--   The PW construction uses the g Sall le perp V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/OrthogonalIsomorphismHolds.lean#L195-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/OrthogonalIsomorphismHolds.lean#L195-L217

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

theorem Formalism.InvariantFactorPaths.PW.gSall_le_perpV (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) {μ ν : Fin n → ℤ} (hne : μ ≠ ν)
    {h' : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hh' : (GAe p LL j e).IsHW ν h') :
    (GAe p LL j e).gS {v | (GAe p LL j e).IsHW μ v} ≤ perpV h' := by sorry
