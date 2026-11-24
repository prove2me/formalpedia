-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_map_prod_add
-- name    : Formalism.L2.FormalSeriesBounds.map_prod_add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:41.435704+00:00
-- url     : https://prove2.me/theorems/ff25a63f-79fa-4b58-a229-b0d51031cd2a
-- title:
--   Formal Series Bounds: map prod add
-- statement:
--   The Formal Series Bounds construction uses the map prod add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieVal.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieVal.lean#L35-L39

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
attribute [instance] LetSys.fin
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.map_prod_add (V : VF C) {α : Type} (s : Finset α) (x : α → C) : V.v (∏ o ∈ s, x o) = ∑ o ∈ s, V.v (x o) := by sorry
