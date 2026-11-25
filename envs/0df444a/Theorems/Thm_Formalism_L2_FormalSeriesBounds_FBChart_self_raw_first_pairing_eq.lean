-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_self_raw_first_pairing_eq
-- name    : Formalism.L2.FormalSeriesBounds.FBChart.self_raw_first_pairing_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:01:09.213403+00:00
-- url     : https://prove2.me/theorems/949a4d67-88d8-4ada-9e5b-17b5689ccfcd
-- title:
--   FBChart: self raw first pairing eq
-- statement:
--   The FBChart construction uses the self raw first pairing eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStabSelf.lean#L71-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStabSelf.lean#L71-L87

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStabSelf
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
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I0 : Type} [Fintype I0]

theorem Formalism.L2.FormalSeriesBounds.FBChart.self_raw_first_pairing_eq (Y : FBChart C V O dd) (p : SelfData Y d I0) (w v : Fin 2 × Fin dd → C) :
    (Y.rawSelf p).sg1 w v = -∑ col, bil Y.h (fun i => w (col, i)) (fun j => v (col, j)) := by sorry
