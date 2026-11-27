-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_PairData_yOf_int
-- name    : Formalism.L2.FormalSeriesBounds.PairData.yOf_int
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:46.821325+00:00
-- url     : https://prove2.me/theorems/b3b97bc4-1a4a-4e61-bfb7-720ce8477706
-- title:
--   Pair Data: y Of int
-- statement:
--   The Pair Data construction uses the y Of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieChar.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieChar.lean#L49-L52

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieTop
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem Formalism.L2.FormalSeriesBounds.PairData.yOf_int {Y : FBChart C V O dd} (p : PairData Y d I) (g : Fin 2) {χ : PS C 1 dd} (h : Y.IsChar χ)
    (x : I g) : V.Ge 0 (p.yOf g χ x) := by sorry
