-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_wtSpC_iff_eig
-- name    : Formalism.InvariantFactorPaths.PW.wtSpC_iff_eig
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:57.116481+00:00
-- url     : https://prove2.me/theorems/b460ca4b-0641-490d-89e1-f23629490ba9
-- title:
--   PW: wt Sp C iff eig
-- statement:
--   The PW construction uses the wt Sp C iff eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CommProjectionHolds.lean#L36-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CommProjectionHolds.lean#L36-L53

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
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

theorem Formalism.InvariantFactorPaths.PW.wtSpC_iff_eig (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ WtSpC p LL j Cs la ↔ ∀ c ∈ Cs, glAct p LL j c c x = ((la c : ℤ) : ℚ_[p]) • x := by sorry
