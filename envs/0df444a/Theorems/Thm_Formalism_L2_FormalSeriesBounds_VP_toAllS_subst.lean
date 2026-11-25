-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_toAllS_subst
-- name    : Formalism.L2.FormalSeriesBounds.VP.toAllS_subst
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:48:17.994589+00:00
-- url     : https://prove2.me/theorems/46802fd7-f295-5bf0-ae2b-9c2707ee9f2b
-- title:
--   VP: to All S subst
-- statement:
--   The VP construction uses the to All S subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValL.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValL.lean#L28-L32

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqSelfOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type}
  [∀ o g, Fintype (I o g)]

theorem Formalism.L2.FormalSeriesBounds.VP.toAllS_subst {κ : Type} [Finite κ] (o : Orb) {E : κ → MvPowerSeries (WV (I o)) C}
    (hE : ∀ x, MvPowerSeries.constantCoeff (E x) = 0) (T : MvPowerSeries κ C) :
    toAllS o (MvPowerSeries.subst E T) = MvPowerSeries.subst (fun x => toAllS o (E x)) T := by sorry
