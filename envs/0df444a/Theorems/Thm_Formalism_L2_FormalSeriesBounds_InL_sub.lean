-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_sub
-- name    : Formalism.L2.FormalSeriesBounds.InL.sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:25:11.891481+00:00
-- url     : https://prove2.me/theorems/df446ca6-2c3d-489b-8b25-f5259072f51f
-- title:
--   In L: sub
-- statement:
--   The In L construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L45-L46

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sub
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.InL.sub {l : ℕ} {f g : PowerSeries C} (hf : InL l f) (hg : InL l g) : InL l (f - g) := by sorry
