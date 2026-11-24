-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_CubeR_map_formal_group_subst
-- name    : Formalism.L2.Th1.A.CubeR.map_formal_group_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:19:52.143072+00:00
-- url     : https://prove2.me/theorems/113d6c7b-8c96-432a-bf5f-ec94cd731bc3
-- title:
--   Cube R: map formal group subst
-- statement:
--   The Cube R construction uses the map formal group subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupConstCoeffZero.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupConstCoeffZero.lean#L32-L38

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb

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

theorem Formalism.L2.Th1.A.CubeR.map_formal_group_subst (φ : A →+* B) (W : WeierstrassCurve A) {a b : MvPowerSeries σ A}
    (ha : cc a = 0) (hb : cc b = 0) :
    MvPowerSeries.map φ (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ A) (fgl W))
      = MvPowerSeries.subst
          (![MvPowerSeries.map φ a, MvPowerSeries.map φ b] : Fin 2 → MvPowerSeries σ B)
          (fgl (W.map φ)) := by sorry
