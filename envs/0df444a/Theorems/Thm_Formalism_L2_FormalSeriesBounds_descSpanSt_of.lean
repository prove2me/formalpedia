-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_descSpanSt_of
-- name    : Formalism.L2.FormalSeriesBounds.descSpanSt_of
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:39:19.039153+00:00
-- url     : https://prove2.me/theorems/ae3b59f5-31aa-4a0b-8503-01d57ea3b457
-- title:
--   Formal Series Bounds: desc Span St of
-- statement:
--   The Formal Series Bounds construction uses the desc Span St of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescSpanSt.lean#L38-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescSpanSt.lean#L38-L101

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
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
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem Formalism.L2.FormalSeriesBounds.descSpanSt_of (hS : HaSpanSt) : DescSpanSt Xo c := by sorry
