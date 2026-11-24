-- Prove2me | Theorems.Thm_Formalism_L2_G_card_quotient_extRing
-- name    : Formalism.L2.G.card_quotient_extRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:20.505143+00:00
-- url     : https://prove2.me/theorems/5ed194af-8920-47c8-94a9-bccadf1e6132
-- title:
--   G: card quotient ext Ring
-- statement:
--   The G construction uses the card quotient ext Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L54-L56

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

theorem Formalism.L2.G.card_quotient_extRing : Nat.card (W2 p n ⧸ Ideal.span {(p : W2 p n)}) = p ^ (2 * n) := by sorry
