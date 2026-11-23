-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Bridge_integral_of_coeff
-- name    : Formalism.L2.Th1.A.Bridge.integral_of_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:12.773746+00:00
-- url     : https://prove2.me/theorems/9d4dea3f-f2c3-4673-8e77-81cf5f88eff6
-- title:
--   Bridge: integral of coeff
-- statement:
--   The Bridge construction uses the integral of coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/BridgeJ.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/BridgeJ.lean#L17-L26

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementJ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeJ
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

theorem Formalism.L2.Th1.A.Bridge.integral_of_coeff {f : K⟦X⟧} (h : ∀ n, coeff n f ∈ Formalism.G.unitBall K) :
    Formalism.DworkPowerSeriesWeights.Integral (ι := Unit) f := by sorry
