-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_relLen_inf
-- name    : Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_inf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:48.448538+00:00
-- url     : https://prove2.me/theorems/f5cb9b32-5d21-4520-8482-19a8a85b4d15
-- title:
--   Idx: rel Len inf
-- statement:
--   The Idx construction uses the rel Len inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L20-L24

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
variable {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]

theorem Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_inf (M N : Submodule O V) : relLen M (M ⊓ N) = relLen M N := by sorry
