-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_pullN_prod
-- name    : Formalism.L2.FormalSeriesBounds.VP.pullN_prod
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:18:16.556998+00:00
-- url     : https://prove2.me/theorems/484a5d83-dd27-4d65-a5a2-1ebc5876ac23
-- title:
--   VP: pull N prod
-- statement:
--   The VP construction uses the pull N prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffSinglePointZero.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffSinglePointZero.lean#L43-L46

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

theorem Formalism.L2.FormalSeriesBounds.VP.pullN_prod {n : ℕ} {ι : Type} (s : Finset ι) (F : ι → PS C n dd) :
    pullN Y p (∏ i ∈ s, F i) = ∏ i ∈ s, pullN Y p (F i) := by sorry
