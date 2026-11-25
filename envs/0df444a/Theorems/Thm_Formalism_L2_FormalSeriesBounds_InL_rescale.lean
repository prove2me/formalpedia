-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_rescale
-- name    : Formalism.L2.FormalSeriesBounds.InL.rescale
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:05.438542+00:00
-- url     : https://prove2.me/theorems/c52dc172-2978-4829-b061-571b1f1104a6
-- title:
--   In L: rescale
-- statement:
--   The In L construction uses the rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L128-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L128-L135

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
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

theorem Formalism.L2.FormalSeriesBounds.InL.rescale {l : ℕ} {ζ : C} (hζ : ζ ^ l = 1) {f : PowerSeries C} (hf : InL l f) :
    PowerSeries.rescale ζ f = f := by sorry
