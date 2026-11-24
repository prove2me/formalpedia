-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Two_subst_tS
-- name    : Formalism.L2.Th1.A.Two.subst_tS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:58.771752+00:00
-- url     : https://prove2.me/theorems/c7a23c28-4b85-4b1e-b16a-a1e42e981efb
-- title:
--   Two: subst t S
-- statement:
--   The Two construction uses the subst t S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/TwoTorsionIntegral.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/TwoTorsionIntegral.lean#L132-L135

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
open Formalism.L2.Th1.A.Two
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)

theorem Formalism.L2.Th1.A.Two.subst_tS (xP : K) : (tS W xP).subst (expSer W)
    = expSer W ^ 2 * (invOfUnit (tDen W xP) 1).subst (expSer W) := by sorry
