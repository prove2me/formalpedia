-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Wp_mul_yZ_sig
-- name    : Formalism.L2.Th1.A.Wp.mul_yZ_sig
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:04.703984+00:00
-- url     : https://prove2.me/theorems/3fd04942-8148-41ec-83b8-173b70d784d1
-- title:
--   Wp: mul y Z sig
-- statement:
--   The Wp construction uses the mul y Z sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ConstCurveDL.lean#L112-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ConstCurveDL.lean#L112-L120

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ConstCurveDL
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
open Formalism.L2.Th1.A.Wp
variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) {e : K⟦X⟧} (he : HasSubst e)
include he

theorem Formalism.L2.Th1.A.Wp.mul_yZ_sig (hne : toL e ≠ 0) :
    toL e * ((toL e)⁻¹ ^ 3 * toL ((yS W).subst e)) = -((toL e)⁻¹ ^ 2 * toL ((xS W).subst e)) := by sorry
