-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_CubeR_pair_vector_map
-- name    : Formalism.L2.Th1.A.CubeR.pair_vector_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:37.952366+00:00
-- url     : https://prove2.me/theorems/02f3b9cf-a783-4ad4-8a9f-88b57dcd5e0f
-- title:
--   Cube R: pair vector map
-- statement:
--   The Cube R construction uses the pair vector map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupConstCoeffZero.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupConstCoeffZero.lean#L23-L26

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

theorem Formalism.L2.Th1.A.CubeR.pair_vector_map (φ : A →+* B) (a b : MvPowerSeries σ A) :
    (fun i => MvPowerSeries.map φ ((![a, b] : Fin 2 → MvPowerSeries σ A) i))
      = ![MvPowerSeries.map φ a, MvPowerSeries.map φ b] := by sorry
