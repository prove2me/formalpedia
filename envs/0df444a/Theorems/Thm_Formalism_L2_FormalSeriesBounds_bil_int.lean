-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_int
-- name    : Formalism.L2.FormalSeriesBounds.bil_int
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:09.517324+00:00
-- url     : https://prove2.me/theorems/daced944-013f-4b4d-bd05-81c5a3cc57a0
-- title:
--   Formal Series Bounds: bil int
-- statement:
--   The Formal Series Bounds construction uses the bil int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L311-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L311-L313

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
variable {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.bil_int {V : VF C} {F : PS C 2 dd} (hF : IntS V F) {w v : Fin dd → C} (hw : ∀ i, V.Ge 0 (w i))
    (hv : ∀ i, V.Ge 0 (v i)) : V.Ge 0 (bil F w v) := by sorry
