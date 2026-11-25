-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_expS_copies
-- name    : Formalism.L2.FormalSeriesBounds.VP.expS_copies
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:23:10.216095+00:00
-- url     : https://prove2.me/theorems/f6b3fbb6-d720-46b4-93f1-586b357abeed
-- title:
--   VP: exp S copies
-- statement:
--   The VP construction uses the exp S copies property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfLogUnitGerm.lean#L21-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfLogUnitGerm.lean#L21-L39

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSProd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm
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

theorem Formalism.L2.FormalSeriesBounds.VP.expS_copies (Y : FBChart C V O dd) (n : ℕ) :
    FB.expS C ((Y.k : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0)) =
      ∏ b : Fin n, ev (n := n) ![pt C dd b] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) := by sorry
