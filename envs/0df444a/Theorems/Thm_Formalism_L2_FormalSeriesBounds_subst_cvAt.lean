-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_cvAt
-- name    : Formalism.L2.FormalSeriesBounds.subst_cvAt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:11:33.858597+00:00
-- url     : https://prove2.me/theorems/7e81dc4a-ed97-4149-9d63-1280ade715a5
-- title:
--   Formal Series Bounds: subst cv At
-- statement:
--   The Formal Series Bounds construction uses the subst cv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L133-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L133-L138

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.subst_cvAt {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {σ : Type} [Finite σ]
    {γ : σ → PowerSeries C} (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0) (F : MvPowerSeries σ C) :
    MvPowerSeries.subst (fun j => cvAt s (γ j)) F = cvAt s (MvPowerSeries.subst γ F) := by sorry
