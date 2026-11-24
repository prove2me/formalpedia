-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_relLen_ne_top_of_le
-- name    : Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_ne_top_of_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:20.296088+00:00
-- url     : https://prove2.me/theorems/5484aa76-168d-4cba-933c-cd8c9aa360b0
-- title:
--   Idx: rel Len ne top of le
-- statement:
--   The Idx construction uses the rel Len ne top of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L175-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L175-L189

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
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]

theorem Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_ne_top_of_le {M N : Submodule O V} (hM : IsLat O K M) (hN : IsLat O K N)
    (hle : N ≤ M) : relLen M N ≠ ⊤ := by sorry
