-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_WpSh_alg_first
-- name    : Formalism.L2.Th1.A.WpSh.alg_first
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:56.142028+00:00
-- url     : https://prove2.me/theorems/f9d1fa5a-488e-4ba2-87ab-a39963da2aba
-- title:
--   Wp Sh: alg first
-- statement:
--   The Wp Sh construction uses the alg first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean#L16-L24

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

theorem Formalism.L2.Th1.A.WpSh.alg_first {S : Type*} [CommRing S] (z zi A B c2 c3 : S) (hz : z * zi = 1)
    (h : (zi ^ 2 * B + (-2) * zi ^ 3 * A) ^ 2 = 4 * (zi ^ 2 * A) ^ 3 - c2 * (zi ^ 2 * A) - c3) :
    (z * B - 2 * A) ^ 2 = 4 * A ^ 3 - c2 * z ^ 4 * A - c3 * z ^ 6 := by sorry
