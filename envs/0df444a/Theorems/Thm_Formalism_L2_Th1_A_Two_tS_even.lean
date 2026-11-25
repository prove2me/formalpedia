-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Two_tS_even
-- name    : Formalism.L2.Th1.A.Two.tS_even
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:16.325177+00:00
-- url     : https://prove2.me/theorems/05290a5c-7ba8-4b91-b231-46b262e6d728
-- title:
--   Two: t S even
-- statement:
--   The Two construction uses the t S even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/TwoTorsionIntegral.lean#L175-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/TwoTorsionIntegral.lean#L175-L183

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

theorem Formalism.L2.Th1.A.Two.tS_even (xP : K) :
    PowerSeries.subst (-X : K⟦X⟧) ((tS W xP).subst (expSer W) : K⟦X⟧)
      = (tS W xP).subst (expSer W) := by sorry
