-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_CurveSer_fw_eq
-- name    : Formalism.L2.Th1.A.CurveSer.fw_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:01.533507+00:00
-- url     : https://prove2.me/theorems/59557e94-31d8-49a6-982e-1972cf1fe095
-- title:
--   Curve Ser: fw eq
-- statement:
--   The Curve Ser construction uses the fw eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean#L94-L97

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
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
open Formalism.L2.Th1.A.CurveSer
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem Formalism.L2.Th1.A.CurveSer.fw_eq : fw W = 1 - C W.a₁ * X - C W.a₂ * X ^ 2
    - X ^ 3 * (2 * C W.a₃ * wU W + 2 * C W.a₄ * X * wU W + 3 * C W.a₆ * wU W * wSer W) := by sorry
