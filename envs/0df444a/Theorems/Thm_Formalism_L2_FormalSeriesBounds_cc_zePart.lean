-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_cc_zePart
-- name    : Formalism.L2.FormalSeriesBounds.cc_zePart
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:08.273097+00:00
-- url     : https://prove2.me/theorems/4776f1d5-2ae3-492a-bc83-5cf6b45ee59c
-- title:
--   Formal Series Bounds: cc ze Part
-- statement:
--   The Formal Series Bounds construction uses the cc ze Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValueEquationOfProjectors.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValueEquationOfProjectors.lean#L124-L127

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValueEquationOfProjectors
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

theorem Formalism.L2.FormalSeriesBounds.cc_zePart (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (s : Orb × Fin 2) (m : Fin dd) :
    MvPowerSeries.constantCoeff (zePart Y p s m) = 0 := by sorry
