-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_toAllS
-- name    : Formalism.L2.FormalSeriesBounds.VP.cc_toAllS
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:50:34.513289+00:00
-- url     : https://prove2.me/theorems/7fc08115-0919-4522-8590-7f789e2b14cc
-- title:
--   VP: cc to All S
-- statement:
--   The VP construction uses the cc to All S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValL.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValL.lean#L23-L26

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqSelfOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type}
  [∀ o g, Fintype (I o g)]

theorem Formalism.L2.FormalSeriesBounds.VP.cc_toAllS (o : Orb) (F : MvPowerSeries (WV (I o)) C) :
    MvPowerSeries.constantCoeff (toAllS o F) = MvPowerSeries.constantCoeff F := by sorry
