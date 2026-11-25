-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_hCol
-- name    : Formalism.L2.FormalSeriesBounds.coeff_hCol
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:20.723375+00:00
-- url     : https://prove2.me/theorems/9204d83d-ee66-4c60-a4b7-1278c1e3fee6
-- title:
--   Formal Series Bounds: coeff h Col
-- statement:
--   The Formal Series Bounds construction uses the coeff h Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStabSelf.lean#L26-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStabSelf.lean#L26-L52

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
variable {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.coeff_hCol (h : PS C 2 dd) (col c1 c2 : Fin 2) (i j : Fin dd) :
    coeff (E2 ((0 : Fin 2), (c1, i)) ((1 : Fin 2), (c2, j))) (hCol col h) =
      if c1 = col ∧ c2 = col then coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h else 0 := by sorry
