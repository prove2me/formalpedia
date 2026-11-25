-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_logCoord_of_dpull
-- name    : Formalism.L2.FormalSeriesBounds.logCoord_of_dpull
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:37:16.323309+00:00
-- url     : https://prove2.me/theorems/98ab850f-bfab-5a33-99ca-474b158ccd97
-- title:
--   Formal Series Bounds: log Coord of dpull
-- statement:
--   The Formal Series Bounds construction uses the log Coord of dpull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LogCoordOfDpull.lean#L102-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LogCoordOfDpull.lean#L102-L121

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
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

theorem Formalism.L2.FormalSeriesBounds.logCoord_of_dpull {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)} (hD : DPullSt Y p) :
    LogCoordSt Y p := by sorry
