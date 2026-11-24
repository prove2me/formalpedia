-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_polProj_glAct
-- name    : Formalism.InvariantFactorPaths.PW.polProj_glAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:01.093352+00:00
-- url     : https://prove2.me/theorems/5a1afa7e-8314-42f0-8116-de7fe0ad7674
-- title:
--   PW: pol Proj gl Act
-- statement:
--   The PW construction uses the pol Proj gl Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/ZpClosedToAddSubgroup.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/ZpClosedToAddSubgroup.lean#L24-L26

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

theorem Formalism.InvariantFactorPaths.PW.polProj_glAct (LL L2 : Letters N) (j : ℕ) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    polProj p r L2 (glAct p LL j c d x) = glAct p LL j c d (polProj p r L2 x) := by sorry
