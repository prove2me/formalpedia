-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_pderiv_rowOf
-- name    : Formalism.L2.FormalSeriesBounds.VP.pderiv_rowOf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:57:01.385843+00:00
-- url     : https://prove2.me/theorems/db6d9c0e-afda-5a6e-9056-ddbeb523aef5
-- title:
--   VP: pderiv row Of
-- statement:
--   The VP construction uses the pderiv row Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PullbackLogCoordsEvalZero.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PullbackLogCoordsEvalZero.lean#L43-L50

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
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
variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

theorem Formalism.L2.FormalSeriesBounds.VP.pderiv_rowOf {n : ℕ} (b b' : Fin n) (w : WVO I) (E : MvPowerSeries (WVO I) C) :
    MvPowerSeries.pderiv C (b, w) (rowOf b' E) = if b' = b then rowOf b (MvPowerSeries.pderiv C w E) else 0 := by sorry
