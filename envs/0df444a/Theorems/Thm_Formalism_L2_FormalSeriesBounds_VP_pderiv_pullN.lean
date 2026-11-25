-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_pderiv_pullN
-- name    : Formalism.L2.FormalSeriesBounds.VP.pderiv_pullN
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:22:40.331413+00:00
-- url     : https://prove2.me/theorems/1ac89c45-7486-4710-a1ab-a201b59c342a
-- title:
--   VP: pderiv pull N
-- statement:
--   The VP construction uses the pderiv pull N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PullbackLogCoordsEvalZero.lean#L93-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PullbackLogCoordsEvalZero.lean#L93-L103

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

theorem Formalism.L2.FormalSeriesBounds.VP.pderiv_pullN {n : ℕ} (b : Fin n) (w : WVO I) (F : PS C n dd) :
    MvPowerSeries.pderiv C (b, w) (pullN Y p F) =
      ∑ j : Fin dd, rowOf b (MvPowerSeries.pderiv C w (expAll Y p j)) *
        pullN Y p (MvPowerSeries.pderiv C (b, j) F) := by sorry
