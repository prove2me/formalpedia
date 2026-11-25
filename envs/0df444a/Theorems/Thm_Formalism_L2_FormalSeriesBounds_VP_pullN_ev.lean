-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_pullN_ev
-- name    : Formalism.L2.FormalSeriesBounds.VP.pullN_ev
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:28:46.832886+00:00
-- url     : https://prove2.me/theorems/c4c5a428-f73b-5e72-97fb-ee5c35f112a0
-- title:
--   VP: pull N ev
-- statement:
--   The VP construction uses the pull N ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffSinglePointZero.lean#L67-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffSinglePointZero.lean#L67-L79

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
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
variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

theorem Formalism.L2.FormalSeriesBounds.VP.pullN_ev {n : ℕ} (b : Fin n) (F : PS C 1 dd) :
    pullN Y p (ev (n := n) ![pt C dd b] F) = rowOf b (pull1 Y p F) := by sorry
