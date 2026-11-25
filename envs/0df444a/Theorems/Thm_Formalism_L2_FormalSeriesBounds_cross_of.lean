-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_cross_of
-- name    : Formalism.L2.FormalSeriesBounds.cross_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:44:01.376175+00:00
-- url     : https://prove2.me/theorems/0f54ee9b-2b77-572a-8632-46f3bd4455dc
-- title:
--   Formal Series Bounds: cross of
-- statement:
--   The Formal Series Bounds construction uses the cross of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean#L129-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean#L129-L192

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
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

theorem Formalism.L2.FormalSeriesBounds.cross_of (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (hE : EndoLogSt Y) (hK : KillSt Y p)
    (hP : ∀ o, ProjSt Y (p o)) : CrossSt Y p := by sorry
