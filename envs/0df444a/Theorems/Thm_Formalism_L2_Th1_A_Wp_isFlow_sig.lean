-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Wp_isFlow_sig
-- name    : Formalism.L2.Th1.A.Wp.isFlow_sig
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:52.304642+00:00
-- url     : https://prove2.me/theorems/9aa75f8d-5fe4-4b88-8b64-eb04f27fd8c0
-- title:
--   Wp: is Flow sig
-- statement:
--   The Wp construction uses the is Flow sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ConstCurveDL.lean#L97-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ConstCurveDL.lean#L97-L109

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

theorem Formalism.L2.Th1.A.Wp.isFlow_sig (hc : ∀ f : K⟦X⟧, derivative K (f.subst e) = (D W f).subst e)
    (hne : toL e ≠ 0) :
    IsFlow (curveL W) dL ((toL e)⁻¹ ^ 2 * toL ((xS W).subst e))
      ((toL e)⁻¹ ^ 3 * toL ((yS W).subst e)) := by sorry
