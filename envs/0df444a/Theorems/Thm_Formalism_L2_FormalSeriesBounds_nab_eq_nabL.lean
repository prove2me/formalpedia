-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_nab_eq_nabL
-- name    : Formalism.L2.FormalSeriesBounds.nab_eq_nabL
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:37.5258+00:00
-- url     : https://prove2.me/theorems/29d75247-9037-4e2b-b00b-c27ba16c1ddb
-- title:
--   Formal Series Bounds: nab eq nab L
-- statement:
--   The Formal Series Bounds construction uses the nab eq nab L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescSpanSt.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescSpanSt.lean#L29-L31

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
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
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.nab_eq_nabL (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) (g : PS C n dd) (P : MvPolynomial (Ls.ι n) C) :
    Y.nab Ls n g P = DescP.nabL (Y.B.FK C) (Ls.cp n) (Ls.uv n) P (gofY Y n) g := by sorry
