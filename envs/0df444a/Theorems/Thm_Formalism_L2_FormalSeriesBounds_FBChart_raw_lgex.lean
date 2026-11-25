-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_raw_lgex
-- name    : Formalism.L2.FormalSeriesBounds.FBChart.raw_lgex
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:10.075083+00:00
-- url     : https://prove2.me/theorems/1f35542d-719a-4437-8774-bed019ad1e78
-- title:
--   FBChart: raw lgex
-- statement:
--   The FBChart construction uses the raw lgex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L143-L147

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

theorem Formalism.L2.FormalSeriesBounds.FBChart.raw_lgex (i : Fin dd) :
    MvPowerSeries.subst (Y.raw p).ex ((Y.raw p).lg i) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by sorry
