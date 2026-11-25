-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_inL_of_rescale
-- name    : Formalism.L2.FormalSeriesBounds.inL_of_rescale
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:16.419211+00:00
-- url     : https://prove2.me/theorems/0f46cc79-8ebe-4a90-8ab3-28a14cc58b0b
-- title:
--   Formal Series Bounds: in L of rescale
-- statement:
--   The Formal Series Bounds construction uses the in L of rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L116-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L116-L126

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

theorem Formalism.L2.FormalSeriesBounds.inL_of_rescale {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) {f : PowerSeries C}
    (h : PowerSeries.rescale ζ f = f) : InL l f := by sorry
