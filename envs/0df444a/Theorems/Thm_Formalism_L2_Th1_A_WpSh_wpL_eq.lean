-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_WpSh_wpL_eq
-- name    : Formalism.L2.Th1.A.WpSh.wpL_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:56.394506+00:00
-- url     : https://prove2.me/theorems/f839a848-f2f2-4d7a-8d8b-d958501e54df
-- title:
--   Wp Sh: wp L eq
-- statement:
--   The Wp Sh construction uses the wp L eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean#L319-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean#L319-L350

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
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
open Formalism.L2.Th1.A.WpSh
variable {K : Type u} [Field K]

theorem Formalism.L2.Th1.A.WpSh.wpL_eq (hE : ExpSpec.{u}) [CharZero K] (W : WeierstrassCurve K) :
    ∃ M : K⟦X⟧, constantCoeff M = 1 ∧ wpL W = uPow (-2) * toL M := by sorry
