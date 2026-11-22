-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_relLen_ne_top
-- name    : Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_ne_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:24.436604+00:00
-- url     : https://prove2.me/theorems/093972c6-c89a-44b8-a9ef-f2526a674ebb
-- title:
--   Idx: rel Len ne top
-- statement:
--   The Idx construction uses the rel Len ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L199-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L199-L202

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
variable [FiniteDimensional K V]

theorem Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_ne_top {M N : Submodule O V} (hM : IsLat O K M) (hN : IsLat O K N) :
    relLen M N ≠ ⊤ := by sorry
