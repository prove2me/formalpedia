-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_ptPl
-- name    : Formalism.L2.FormalSeriesBounds.VP.cc_ptPl
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:35:01.31451+00:00
-- url     : https://prove2.me/theorems/114e0ddf-a0bd-503a-9207-5929a5038a83
-- title:
--   VP: cc pt Pl
-- statement:
--   The VP construction uses the cc pt Pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GermLiftSelfSt.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GermLiftSelfSt.lean#L83-L86

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

theorem Formalism.L2.FormalSeriesBounds.VP.cc_ptPl (ρ : Fin N) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff ((![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] : Fin 2 → Pt C n dd) q.1 q.2) = 0 := by sorry
