-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_IsIU_prod
-- name    : Formalism.L2.FormalSeriesBounds.IsIU.prod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:04.105573+00:00
-- url     : https://prove2.me/theorems/5ffe7a49-127b-5e4f-ba40-72f040fe5d41
-- title:
--   Is IU: prod
-- statement:
--   The Is IU construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValU.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValU.lean#L30-L37

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod

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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

theorem Formalism.L2.FormalSeriesBounds.IsIU.prod {σ ι : Type} (s : Finset ι) {U : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IsIU V (U i)) :
    IsIU V (∏ i ∈ s, U i) := by sorry
