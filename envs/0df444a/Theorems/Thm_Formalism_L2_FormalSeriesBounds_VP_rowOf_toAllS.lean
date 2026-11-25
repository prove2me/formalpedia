-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_rowOf_toAllS
-- name    : Formalism.L2.FormalSeriesBounds.VP.rowOf_toAllS
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:32.111839+00:00
-- url     : https://prove2.me/theorems/f2622b42-e492-50a1-abc9-da119d1d8b5f
-- title:
--   VP: row Of to All S
-- statement:
--   The VP construction uses the row Of to All S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffSinglePointZero.lean#L100-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffSinglePointZero.lean#L100-L108

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_rename

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
variable {n : ℕ}

theorem Formalism.L2.FormalSeriesBounds.VP.rowOf_toAllS (b : Fin n) (o : Orb) (F : MvPowerSeries (WV (I o)) C) :
    rowOf b (toAllS o F) = MvPowerSeries.rename (eAll n o) (rowCopy b F) := by sorry
