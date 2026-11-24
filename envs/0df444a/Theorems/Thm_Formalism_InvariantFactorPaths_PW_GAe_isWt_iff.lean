-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_isWt_iff
-- name    : Formalism.InvariantFactorPaths.PW.GAe_isWt_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:37.799178+00:00
-- url     : https://prove2.me/theorems/a70c1acf-3f01-4bd8-8433-c2c9b5caa0de
-- title:
--   PW: GAe is Wt iff
-- statement:
--   The PW construction uses the GAe is Wt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L130-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L130-L153

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

theorem Formalism.InvariantFactorPaths.PW.GAe_isWt_iff (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) (μ : Fin n → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GAe p LL j e).IsWt μ x ↔ x ∈ MvPolynomial.restrictSupport ℚ_[p] {m | ∀ a, wt LL j (e a) m = μ a} := by sorry
