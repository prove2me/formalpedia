-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_axisAll
-- name    : Formalism.L2.FormalSeriesBounds.FBChart.axisAll
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:46:39.777113+00:00
-- url     : https://prove2.me/theorems/24254b53-4830-45da-9e4e-f9d6592cf98f
-- title:
--   FBChart: axis All
-- statement:
--   The FBChart construction uses the axis All property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L446-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L446-L456

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
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
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.FBChart.axisAll (Y : FBChart C V O dd) (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ)
    (he : ∀ s ∈ e.support, s.1 ≠ g) : coeff e Y.h = 0 := by sorry
