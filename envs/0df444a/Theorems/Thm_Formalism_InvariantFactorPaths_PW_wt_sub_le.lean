-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_wt_sub_le
-- name    : Formalism.InvariantFactorPaths.PW.wt_sub_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:29.16153+00:00
-- url     : https://prove2.me/theorems/a107c7c8-ddd3-4906-9ad2-a54eefe59269
-- title:
--   PW: wt sub le
-- statement:
--   The PW construction uses the wt sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L248-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L248-L260

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

theorem Formalism.InvariantFactorPaths.PW.wt_sub_le (LL L2 : Letters N) (j : ℕ) (c : Fin r) {m m' : Fin N × Fin r →₀ ℕ}
    (hm : MultiDeg L2 m) (hm' : MultiDeg L2 m') : wt LL j c m' - wt LL j c m ≤ (L2.total : ℤ) := by sorry
