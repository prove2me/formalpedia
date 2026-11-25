-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_wtSpC_mono
-- name    : Formalism.InvariantFactorPaths.PW.wtSpC_mono
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:37:07.249802+00:00
-- url     : https://prove2.me/theorems/43f96fb3-3c5c-40fb-a83a-c27b2f43830a
-- title:
--   PW: wt Sp C mono
-- statement:
--   The PW construction uses the wt Sp C mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L98-L102

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

theorem Formalism.InvariantFactorPaths.PW.wtSpC_mono (LL : Letters N) (j : ℕ) {Cs Cs' : Finset (Fin r)} (h : Cs ⊆ Cs') (la : Fin r → ℤ) :
    WtSpC p LL j Cs' la ≤ WtSpC p LL j Cs la := by sorry
