-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_E2_sum_hCol_eq_ite
-- name    : Formalism.L2.FormalSeriesBounds.coeff_E2_sum_hCol_eq_ite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:07:35.502876+00:00
-- url     : https://prove2.me/theorems/ae89a58d-29ff-43dd-a349-b84207031201
-- title:
--   Formal Series Bounds: coeff E2 sum h Col eq ite
-- statement:
--   The Formal Series Bounds construction uses the coeff E2 sum h Col eq ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStabSelf.lean#L60-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStabSelf.lean#L60-L69

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

theorem Formalism.L2.FormalSeriesBounds.coeff_E2_sum_hCol_eq_ite (h : PS C 2 dd) (c1 c2 : Fin 2) (i j : Fin dd) :
    coeff (E2 ((0 : Fin 2), (c1, i)) ((1 : Fin 2), (c2, j))) (∑ col, hCol col h) =
      if c1 = c2 then coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h else 0 := by sorry
