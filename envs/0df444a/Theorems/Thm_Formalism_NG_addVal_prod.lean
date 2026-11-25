-- Prove2me | Theorems.Thm_Formalism_NG_addVal_prod
-- name    : Formalism.NG.addVal_prod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:17.260951+00:00
-- url     : https://prove2.me/theorems/887b71b1-8cd9-5f12-9014-35755a63bfa6
-- title:
--   NG: add Val prod
-- statement:
--   The NG construction uses the add Val prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/Assemble.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/Assemble.lean#L9-L15

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.NG
universe uO uT uT' uΩ uR

theorem Formalism.NG.addVal_prod {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ι : Type*} (s : Finset ι) (f : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, f i) = ∑ i ∈ s, IsDiscreteValuationRing.addVal O (f i) := by sorry
