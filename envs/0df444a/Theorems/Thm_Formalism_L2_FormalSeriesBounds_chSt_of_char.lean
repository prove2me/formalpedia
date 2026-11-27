-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_chSt_of_char
-- name    : Formalism.L2.FormalSeriesBounds.chSt_of_char
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T04:59:30.799175+00:00
-- url     : https://prove2.me/theorems/932abb59-147a-5542-9f43-230a23aec54e
-- title:
--   Formal Series Bounds: ch St of char
-- statement:
--   The Formal Series Bounds construction uses the ch St of char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieChar.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieChar.lean#L71-L77

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieTop
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem Formalism.L2.FormalSeriesBounds.chSt_of_char [NeZero d] (hG : CharGermSt) (Y : FBChart C V O dd) (p : PairData Y d I) (h : CHCharSt Y p)
    (Hc : ∀ g, (Y.raw p).CartHyp V g) : RawChart.CHSt Hc := by sorry
