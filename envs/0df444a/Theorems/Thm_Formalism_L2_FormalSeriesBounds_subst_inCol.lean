-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_inCol
-- name    : Formalism.L2.FormalSeriesBounds.subst_inCol
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:56.234231+00:00
-- url     : https://prove2.me/theorems/75c23295-7714-4a3c-8ff5-6921d3c7d75a
-- title:
--   Formal Series Bounds: subst in Col
-- statement:
--   The Formal Series Bounds construction uses the subst in Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePCartSelfSt.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePCartSelfSt.lean#L26-L34

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
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
variable {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.subst_inCol {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : ∀ x, constantCoeff (a x) = 0)
    (col : Fin 2) (f : MvPowerSeries (Fin dd) C) :
    subst a (inCol col f) = subst (fun i => a (col, i)) f := by sorry
