-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_CubeR_three_univ
-- name    : Formalism.L2.Th1.A.CubeR.three_univ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:31.525576+00:00
-- url     : https://prove2.me/theorems/9367878d-334e-4ad6-9323-938f0cbd21e7
-- title:
--   Cube R: three univ
-- statement:
--   The Cube R construction uses the three univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupConstCoeffZero.lean#L173-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupConstCoeffZero.lean#L173-L184

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.CubeR
open Univ CurveSer
local notation "cc" => MvPowerSeries.constantCoeff
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] (W : WeierstrassCurve A)

theorem Formalism.L2.Th1.A.CubeR.three_univ : ∃ e : MvPowerSeries (Fin 3) Z, cc e = -1 ∧
    lhs3 W₀ = e * sum3 W₀ * (MvPowerSeries.X 0 - MvPowerSeries.X 1)
      * (MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2) := by sorry
