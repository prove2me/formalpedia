-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_inL_subst
-- name    : Formalism.L2.FormalSeriesBounds.inL_subst
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:18.232056+00:00
-- url     : https://prove2.me/theorems/ec911a6a-7675-45fa-bf02-d4c13a5a8580
-- title:
--   Formal Series Bounds: in L subst
-- statement:
--   The Formal Series Bounds construction uses the in L subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L31-L33

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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

theorem Formalism.L2.FormalSeriesBounds.inL_subst {l : ℕ} (hl : 0 < l) (f : PowerSeries C) :
    InL l (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) := by sorry
