-- Prove2me | Theorems.Thm_Formalism_L2_G_card_quot_WQ
-- name    : Formalism.L2.G.card_quot_WQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:16.442273+00:00
-- url     : https://prove2.me/theorems/6c1b0b23-63d1-43cf-8b48-7ca611acdf39
-- title:
--   G: card quot WQ
-- statement:
--   The G construction uses the card quot WQ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L50-L52

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

theorem Formalism.L2.G.card_quot_WQ : Nat.card (WQ p n ⧸ Ideal.span {(p : WQ p n)}) = p ^ n := by sorry
