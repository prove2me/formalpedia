-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_dpull_of_ode
-- name    : Formalism.L2.FormalSeriesBounds.dpull_of_ode
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:57:11.865144+00:00
-- url     : https://prove2.me/theorems/a4384946-88f3-572b-96c9-0b83a1b2cfc7
-- title:
--   Formal Series Bounds: dpull of ode
-- statement:
--   The Formal Series Bounds construction uses the dpull of ode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PullbackLogCoordsEvalZero.lean#L107-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PullbackLogCoordsEvalZero.lean#L107-L143

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

theorem Formalism.L2.FormalSeriesBounds.dpull_of_ode {Y : FBChart C V O dd} (p : ∀ o, PairData Y d (I o)) (hE : ExpODESt Y) : DPullSt Y p := by sorry
