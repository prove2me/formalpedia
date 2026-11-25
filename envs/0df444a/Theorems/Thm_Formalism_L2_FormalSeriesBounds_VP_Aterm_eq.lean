-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_Aterm_eq
-- name    : Formalism.L2.FormalSeriesBounds.VP.Aterm_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:45:30.386232+00:00
-- url     : https://prove2.me/theorems/9b452af8-c7e8-4c3d-8ba2-be3af31206f3
-- title:
--   VP: Aterm eq
-- statement:
--   The VP construction uses the Aterm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfBiadditiveCross.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfBiadditiveCross.lean#L17-L22

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_TripleSubstSecondCoordinate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfBiadditiveCross
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mvExp

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
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
open Formalism.L2.FormalSeriesBounds.VP

theorem Formalism.L2.FormalSeriesBounds.VP.Aterm_eq (Y : FBChart C V O dd) (π : Orb → Fin 2 → Fin dd → PS C 1 dd)
    (hπ0 : ∀ o g i, MvPowerSeries.constantCoeff (π o g i) = 0) (s s' : Orb × Fin 2) :
    Aterm Y π s s' = mvExp ((Y.k : C) • hAt Y (π s.1 s.2) (actAt Y Y.w0 (π s'.1 s'.2))) := by sorry
