-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_of_clearedM
-- name    : Formalism.L2.Th1.A.WpSh.cleared_of_clearedM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:30.130124+00:00
-- url     : https://prove2.me/theorems/7f4baaa2-ed0d-4f04-a31c-4c7f9666fd18
-- title:
--   Wp Sh: cleared of cleared M
-- statement:
--   The Wp Sh construction uses the cleared of cleared M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean#L137-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean#L137-L145

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

theorem Formalism.L2.Th1.A.WpSh.cleared_of_clearedM {g2 g3 : K} {r : K⟦X⟧} (h : ClearedM g2 g3 (1 + X ^ 2 * r)) :
    Cleared g2 g3 r := by sorry
