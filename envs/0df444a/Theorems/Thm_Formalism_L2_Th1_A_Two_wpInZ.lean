-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Two_wpInZ
-- name    : Formalism.L2.Th1.A.Two.wpInZ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:07.137841+00:00
-- url     : https://prove2.me/theorems/d4157580-ccdd-42c8-b04e-e557c3a87b44
-- title:
--   Two: wp In Z
-- statement:
--   The Two construction uses the wp In Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/TwoTorsionIntegral.lean#L300-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/TwoTorsionIntegral.lean#L300-L309

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Two
open Formalism.L2.Th1.A.Two
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)

theorem Formalism.L2.Th1.A.Two.wpInZ (hS : WpShape.{u}) : expSer W ^ 2 * (1 + X ^ 2 * wpReg W)
    = X ^ 2 * ((xS W).subst (expSer W) + C (W.b₂ / 12) * expSer W ^ 2) := by sorry
