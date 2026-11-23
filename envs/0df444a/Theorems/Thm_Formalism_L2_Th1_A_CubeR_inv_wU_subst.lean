-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_CubeR_inv_wU_subst
-- name    : Formalism.L2.Th1.A.CubeR.inv_wU_subst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:19:36.7348+00:00
-- url     : https://prove2.me/theorems/2c6542ef-8aca-4d58-b4d5-8fe2f417cd01
-- title:
--   Cube R: inv w U subst
-- statement:
--   The Cube R construction uses the inv w U subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupConstCoeffZero.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupConstCoeffZero.lean#L52-L62

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
variable {σ : Type*} {A : Type u} {B : Type v} [CommRing A] [CommRing B]

theorem Formalism.L2.Th1.A.CubeR.inv_wU_subst {K : Type u} [Field K] (W : WeierstrassCurve K) {a : MvPowerSeries σ K}
    (ha : cc a = 0) : ((Formalism.ELL.wU (wSer W)).subst a)⁻¹ = (xS W).subst a := by sorry
