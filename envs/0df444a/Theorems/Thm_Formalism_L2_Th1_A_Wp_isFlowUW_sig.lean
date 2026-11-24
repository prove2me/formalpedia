-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Wp_isFlowUW_sig
-- name    : Formalism.L2.Th1.A.Wp.isFlowUW_sig
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:51.461744+00:00
-- url     : https://prove2.me/theorems/9c23ca55-873f-42e3-979b-ca4868bde6e8
-- title:
--   Wp: is Flow UW sig
-- statement:
--   The Wp construction uses the is Flow UW sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ConstCurveDL.lean#L64-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ConstCurveDL.lean#L64-L85

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

theorem Formalism.L2.Th1.A.Wp.isFlowUW_sig (hc : ∀ f : K⟦X⟧, derivative K (f.subst e) = (D W f).subst e) :
    IsFlowUW (curveL W) dL (sig he X) (sig he (wSer W)) := by sorry
