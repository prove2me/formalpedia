-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_weylLat_div
-- name    : Formalism.InvariantFactorPaths.PW.weylLat_div
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:46.844226+00:00
-- url     : https://prove2.me/theorems/ab5022ab-3618-4c4e-9614-c49282606386
-- title:
--   PW: weyl Lat div
-- statement:
--   The PW construction uses the weyl Lat div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/ZpClosedToAddSubgroup.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/ZpClosedToAddSubgroup.lean#L53-L57

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_ZpClosedToAddSubgroup
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

theorem Formalism.InvariantFactorPaths.PW.weylLat_div (LL : Letters N) (j : ℕ) (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (c d : Fin r) (hcd : c ≠ d)
    (k : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ WeylLat p LL j h) :
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p LL j c d) ^ k) x ∈ WeylLat p LL j h := by sorry
