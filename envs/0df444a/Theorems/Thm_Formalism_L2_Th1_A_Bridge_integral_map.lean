-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Bridge_integral_map
-- name    : Formalism.L2.Th1.A.Bridge.integral_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:18.834032+00:00
-- url     : https://prove2.me/theorems/f61764a4-1c63-4d4f-97e9-af032312208c
-- title:
--   Bridge: integral map
-- statement:
--   The Bridge construction uses the integral map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/BridgeJ.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/BridgeJ.lean#L34-L39

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementJ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeJ
import Theorems.Thm_Formalism_ELL_EulerSeries_integral_map
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_integral_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Bridge
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.L2.Th1.A.Bridge.integral_map {ι : Type} (c : MvPowerSeries ι (Formalism.G.unitBall K)) :
    Formalism.DworkPowerSeriesWeights.Integral (MvPowerSeries.map (Formalism.G.unitBall K).subtype c) := by sorry
