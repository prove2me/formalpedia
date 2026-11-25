-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_lowC_le_perpV
-- name    : Formalism.InvariantFactorPaths.PW.lowC_le_perpV
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:44:38.916818+00:00
-- url     : https://prove2.me/theorems/34efd69b-f926-5a64-809e-7bae386a166a
-- title:
--   PW: low C le perp V
-- statement:
--   The PW construction uses the low C le perp V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L116-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L116-L123

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

theorem Formalism.InvariantFactorPaths.PW.lowC_le_perpV (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    {h : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hh : h ∈ HWC p LL j Cs la) : lowC p LL j Cs ≤ perpV h := by sorry
