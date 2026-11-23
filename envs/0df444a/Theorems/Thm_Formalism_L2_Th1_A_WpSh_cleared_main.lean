-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_main
-- name    : Formalism.L2.Th1.A.WpSh.cleared_main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:39.79549+00:00
-- url     : https://prove2.me/theorems/b9b089d5-18e9-4d37-9691-8d45b8dbeec8
-- title:
--   Wp Sh: cleared main
-- statement:
--   The Wp Sh construction uses the cleared main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean#L153-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean#L153-L160

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

theorem Formalism.L2.Th1.A.WpSh.cleared_main {g2 g3 : K} {r : K⟦X⟧} (h : Cleared g2 g3 r) :
    4 * (X * derivative K r) + 12 * r =
      X ^ 2 * (C g2 + C g3 * X ^ 2 + C g2 * X ^ 2 * r - 12 * r ^ 2 - 4 * X ^ 2 * r ^ 3
        + X ^ 2 * derivative K r ^ 2) := by sorry
