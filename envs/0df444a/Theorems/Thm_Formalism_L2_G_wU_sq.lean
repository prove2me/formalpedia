-- Prove2me | Theorems.Thm_Formalism_L2_G_wU_sq
-- name    : Formalism.L2.G.wU_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:16:42.962384+00:00
-- url     : https://prove2.me/theorems/6d8bf0d2-6e38-4f5e-8c07-6e73fe8e0646
-- title:
--   G: w U sq
-- statement:
--   The G construction uses the w U sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/JOInjective.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/JOInjective.lean#L35-L37

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_AlgebraMapFinite
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_JOInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
open QuadraticAlgebra Formalism.BasicNotions.Examples₂ Formalism.MainNotions.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

theorem Formalism.L2.G.wU_sq : wU p n ^ 2 = (p : OO p n) := by sorry
