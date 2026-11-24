-- Prove2me | Theorems.Thm_Formalism_L2_G_sq_OO
-- name    : Formalism.L2.G.sq_OO
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:18:05.277575+00:00
-- url     : https://prove2.me/theorems/a7895475-c7e6-4b2f-9e1d-6c7643feb6ab
-- title:
--   G: sq OO
-- statement:
--   The G construction uses the sq OO property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/JOInjective.lean#L39-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/JOInjective.lean#L39-L50

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

theorem Formalism.L2.G.sq_OO [NeZero n] (hp2 : p ≠ 2) (z : ℤ) : ∃ y : OO p n, y ^ 2 = (z : OO p n) := by sorry
