-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_rawSelf_lgex
-- name    : Formalism.L2.FormalSeriesBounds.FBChart.rawSelf_lgex
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:53:18.333221+00:00
-- url     : https://prove2.me/theorems/47f7890f-5a73-46ee-a9ca-c0ab487800ec
-- title:
--   FBChart: raw Self lgex
-- statement:
--   The FBChart construction uses the raw Self lgex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePCartSelfSt.lean#L93-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePCartSelfSt.lean#L93-L103

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ}
  {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

theorem Formalism.L2.FormalSeriesBounds.FBChart.rawSelf_lgex (x : Fin 2 × Fin dd) :
    subst (Y.rawSelf p).ex ((Y.rawSelf p).lg x) = (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by sorry
