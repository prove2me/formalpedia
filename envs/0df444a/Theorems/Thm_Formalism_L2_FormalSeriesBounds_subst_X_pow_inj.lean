-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_X_pow_inj
-- name    : Formalism.L2.FormalSeriesBounds.subst_X_pow_inj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:25:26.5471+00:00
-- url     : https://prove2.me/theorems/02013cc8-26a5-4dd1-8195-b66a4dbd7311
-- title:
--   Formal Series Bounds: subst X pow inj
-- statement:
--   The Formal Series Bounds construction uses the subst X pow inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L35-L40

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

theorem Formalism.L2.FormalSeriesBounds.subst_X_pow_inj {l : ℕ} (hl : 0 < l) {f g : PowerSeries C}
    (h : PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) g) : f = g := by sorry
