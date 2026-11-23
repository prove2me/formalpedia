-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Bridge_integral_of_mvCoeff
-- name    : Formalism.L2.Th1.A.Bridge.integral_of_mvCoeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:14.144379+00:00
-- url     : https://prove2.me/theorems/6711a5c3-2eb3-4688-9ca6-29e445041887
-- title:
--   Bridge: integral of mv Coeff
-- statement:
--   The Bridge construction uses the integral of mv Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/BridgeJ.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/BridgeJ.lean#L28-L32

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

theorem Formalism.L2.Th1.A.Bridge.integral_of_mvCoeff {ι : Type} {f : MvPowerSeries ι K}
    (h : ∀ n, MvPowerSeries.coeff n f ∈ Formalism.G.unitBall K) : Formalism.DworkPowerSeriesWeights.Integral f := by sorry
