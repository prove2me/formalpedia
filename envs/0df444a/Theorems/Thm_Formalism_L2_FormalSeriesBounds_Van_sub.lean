-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_sub
-- name    : Formalism.L2.FormalSeriesBounds.Van.sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:46:39.35246+00:00
-- url     : https://prove2.me/theorems/8f950b84-f2c4-495a-a8a6-15a538ea5b96
-- title:
--   Van: sub
-- statement:
--   The Van construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L18-L20

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sub

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {τ : Type}

theorem Formalism.L2.FormalSeriesBounds.Van.sub {T : Set τ} {f g : MvPowerSeries τ C} (hf : Van T f) (hg : Van T g) : Van T (f - g) := by sorry
