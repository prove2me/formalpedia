-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_zpClosed_toAddSubgroup
-- name    : Formalism.InvariantFactorPaths.PW.zpClosed_toAddSubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:38:58.224549+00:00
-- url     : https://prove2.me/theorems/cb657609-4c0e-43d1-9c83-8d52246cea6a
-- title:
--   PW: zp Closed to Add Subgroup
-- statement:
--   The PW construction uses the zp Closed to Add Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/ZpClosedToAddSubgroup.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/ZpClosedToAddSubgroup.lean#L59-L68

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

theorem Formalism.InvariantFactorPaths.PW.zpClosed_toAddSubgroup {W : Type} [AddCommGroup W] [Module ℚ_[p] W] [Module ℤ_[p] W]
    [IsScalarTower ℤ_[p] ℚ_[p] W] (L : Submodule ℤ_[p] W) : ZpClosed p L.toAddSubgroup := by sorry
