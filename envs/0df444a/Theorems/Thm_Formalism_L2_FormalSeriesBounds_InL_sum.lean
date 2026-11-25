-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_sum
-- name    : Formalism.L2.FormalSeriesBounds.InL.sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:45.728792+00:00
-- url     : https://prove2.me/theorems/8279b9f6-ec7b-4c36-ac5e-99b38b06019f
-- title:
--   In L: sum
-- statement:
--   The In L construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L54-L58

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum

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

theorem Formalism.L2.FormalSeriesBounds.InL.sum {l : ℕ} {ι : Type} (s : Finset ι) (f : ι → PowerSeries C) (hf : ∀ i ∈ s, InL l (f i)) :
    InL l (∑ i ∈ s, f i) := by sorry
