-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_length_quot_range
-- name    : Formalism.IrreducibleCountingLemmas.TW.Idx.length_quot_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:08.358279+00:00
-- url     : https://prove2.me/theorems/9f43d76b-89a7-40f3-96a2-835936c2ab65
-- title:
--   Idx: length quot range
-- statement:
--   The Idx construction uses the length quot range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L72-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L72-L99

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

theorem Formalism.IrreducibleCountingLemmas.TW.Idx.length_quot_range {B ι : Type} [AddCommGroup B] [Module O B] [Fintype ι]
    (b : Basis ι O B) (f : B →ₗ[O] B) (hf : Function.Injective f) :
    Module.length O (B ⧸ LinearMap.range f) = Ring.ord O (LinearMap.det f) := by sorry
