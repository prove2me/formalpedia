-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_wtSpC_iff
-- name    : Formalism.InvariantFactorPaths.PW.wtSpC_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:34.62495+00:00
-- url     : https://prove2.me/theorems/bfc59416-e01b-4831-a63b-99e58c5cd4aa
-- title:
--   PW: wt Sp C iff
-- statement:
--   The PW construction uses the wt Sp C iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L165-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L165-L177

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
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

theorem Formalism.InvariantFactorPaths.PW.wtSpC_iff (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ WtSpC p LL j Cs la ↔ (GAe p LL j (enumC Cs)).IsWt (la ∘ enumC Cs) x := by sorry
