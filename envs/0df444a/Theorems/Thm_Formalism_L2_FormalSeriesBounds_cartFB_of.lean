-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_cartFB_of
-- name    : Formalism.L2.FormalSeriesBounds.cartFB_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:07.385627+00:00
-- url     : https://prove2.me/theorems/45ab70a0-0163-4151-8457-43c83ba56ca1
-- title:
--   Formal Series Bounds: cart FB of
-- statement:
--   The Formal Series Bounds construction uses the cart FB of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L176-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L176-L201

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.cartFB_of (hPT : PTFBSt) (hAdd : AddCvFBSt) (hStab : HStabFBSt) : CartFBSt := by sorry
