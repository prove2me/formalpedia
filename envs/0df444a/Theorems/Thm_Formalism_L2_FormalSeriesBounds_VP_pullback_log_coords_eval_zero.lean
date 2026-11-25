-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_pullback_log_coords_eval_zero
-- name    : Formalism.L2.FormalSeriesBounds.VP.pullback_log_coords_eval_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:57:17.717644+00:00
-- url     : https://prove2.me/theorems/b7a1b2bf-7713-572e-b333-75d616258a58
-- title:
--   VP: pullback log coords eval zero
-- statement:
--   The VP construction uses the pullback log coords eval zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PullbackLogCoordsEvalZero.lean#L59-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PullbackLogCoordsEvalZero.lean#L59-L91

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
open Formalism.L2.FormalSeriesBounds.VP
variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

theorem Formalism.L2.FormalSeriesBounds.VP.pullback_log_coords_eval_zero {n : ℕ} (b : Fin n) (G : PS C 2 dd) :
    pullN Y p (ev (n := n) ![pt C dd b, 0] G) =
      rowOf b (MvPowerSeries.subst (linS (Mu Y p)) (MvPowerSeries.subst (exZero Y) G)) := by sorry
