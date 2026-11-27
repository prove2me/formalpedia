-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_agr_subst_right
-- name    : Formalism.L2.FormalSeriesBounds.agr_subst_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:40.864181+00:00
-- url     : https://prove2.me/theorems/e9ef7784-a76c-5dd2-9d10-8e5a3fc4aebd
-- title:
--   Formal Series Bounds: agr subst right
-- statement:
--   The Formal Series Bounds construction uses the agr subst right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L53-L57

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

theorem Formalism.L2.FormalSeriesBounds.agr_subst_right {σ τ : Type} [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) {k : ℕ} {f g : MvPowerSeries σ C} (h : Agr k f g) :
    Agr k (MvPowerSeries.subst a f) (MvPowerSeries.subst a g) := by sorry
