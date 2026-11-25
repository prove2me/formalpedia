-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_pullS_off
-- name    : Formalism.L2.FormalSeriesBounds.VP.pullS_off
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:35:28.915081+00:00
-- url     : https://prove2.me/theorems/3f6ecf7d-20cf-5ef6-9686-ce9c2b140b64
-- title:
--   VP: pull S off
-- statement:
--   The VP construction uses the pull S off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GermLiftSelfSt.lean#L144-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GermLiftSelfSt.lean#L144-L161

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GermLiftSelfSt
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
open Formalism.L2.FormalSeriesBounds.VP
variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n)

theorem Formalism.L2.FormalSeriesBounds.VP.pullS_off (b : Fin n) (hb : b ∉ Set.range pl) (E : PS C 1 dd) :
    pullS Y p pl (ev (n := n) ![pt C dd b] E) = MvPowerSeries.C (MvPowerSeries.constantCoeff E) := by sorry
