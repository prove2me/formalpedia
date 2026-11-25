-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_biadd_of_sum
-- name    : Formalism.L2.FormalSeriesBounds.biadd_of_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:18:18.945432+00:00
-- url     : https://prove2.me/theorems/3be4af4e-ce20-5b9f-89d5-d8a26d5ea3f2
-- title:
--   Formal Series Bounds: biadd of sum
-- statement:
--   The Formal Series Bounds construction uses the biadd of sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoordinateChangeComp1IntertwinesAction.lean#L118-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoordinateChangeComp1IntertwinesAction.lean#L118-L177

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
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

theorem Formalism.L2.FormalSeriesBounds.biadd_of_sum (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (hS : SumProjSt Y p) : BiaddSt Y p := by sorry
