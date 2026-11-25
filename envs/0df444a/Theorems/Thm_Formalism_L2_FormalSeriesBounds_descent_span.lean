-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_descent_span
-- name    : Formalism.L2.FormalSeriesBounds.descent_span
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:33.76437+00:00
-- url     : https://prove2.me/theorems/34415f2c-2074-480e-b7ac-95b701bd9dde
-- title:
--   Formal Series Bounds: descent span
-- statement:
--   The Formal Series Bounds construction uses the descent span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescSpanFinal.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescSpanFinal.lean#L14-L15

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaLeaves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanFinal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem Formalism.L2.FormalSeriesBounds.descent_span : DescSpanSt Xo c := by sorry
