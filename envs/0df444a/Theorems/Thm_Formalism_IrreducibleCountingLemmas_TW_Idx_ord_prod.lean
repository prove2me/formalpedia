-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_ord_prod
-- name    : Formalism.IrreducibleCountingLemmas.TW.Idx.ord_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:17.345794+00:00
-- url     : https://prove2.me/theorems/765637a5-89ad-4339-bfc1-13cc3ca0c59b
-- title:
--   Idx: ord prod
-- statement:
--   The Idx construction uses the ord prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L63-L70

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
open Formalism.IrreducibleCountingLemmas.TW.Idx
variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]

theorem Formalism.IrreducibleCountingLemmas.TW.Idx.ord_prod {ι : Type} (s : Finset ι) (a : ι → O) (ha : ∀ i, a i ≠ 0) :
    Ring.ord O (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord O (a i) := by sorry
