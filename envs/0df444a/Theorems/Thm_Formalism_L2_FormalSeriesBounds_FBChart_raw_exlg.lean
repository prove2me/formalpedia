-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_raw_exlg
-- name    : Formalism.L2.FormalSeriesBounds.FBChart.raw_exlg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:28.520086+00:00
-- url     : https://prove2.me/theorems/ba789336-08a2-4dc5-a497-94d5fbab60c2
-- title:
--   FBChart: raw exlg
-- statement:
--   The FBChart construction uses the raw exlg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L137-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L137-L141

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

theorem Formalism.L2.FormalSeriesBounds.FBChart.raw_exlg (i : Fin dd) :
    MvPowerSeries.subst (Y.raw p).lg ((Y.raw p).ex i) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by sorry
