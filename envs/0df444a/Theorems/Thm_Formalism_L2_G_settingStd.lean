-- Prove2me | Theorems.Thm_Formalism_L2_G_settingStd
-- name    : Formalism.L2.G.settingStd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:16:36.841843+00:00
-- url     : https://prove2.me/theorems/00e5f582-9357-4280-995e-cdaee712675c
-- title:
--   G: setting Std
-- statement:
--   The G construction uses the setting Std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/JOInjective.lean#L52-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/JOInjective.lean#L52-L74

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

theorem Formalism.L2.G.settingStd (h5 : 5 ≤ p) (h2 : 2 ≤ n) (he : Even n) :
    UnramifiedQuadraticSetting p n (WQ p n) (QQ p n) (OO p n) (KO p n) (iota p n) (sig p n) (jO p n) (wU p n) := by sorry
