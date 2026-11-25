-- Prove2me | Theorems.Thm_Formalism_L2_G_jW_natCast
-- name    : Formalism.L2.G.jW_natCast
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:44:52.686319+00:00
-- url     : https://prove2.me/theorems/e6d8f328-81fe-5035-93cd-d119542f5462
-- title:
--   G: j W nat Cast
-- statement:
--   The G construction uses the j W nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L174-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L174-L174

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
omit [NeZero n]

theorem Formalism.L2.G.jW_natCast : jW p n (p : WQ p n) = (p : W2 p n) := by sorry
