-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_ord_unit_mul_pow
-- name    : Formalism.IrreducibleCountingLemmas.TW.Idx.ord_unit_mul_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:07:18.004669+00:00
-- url     : https://prove2.me/theorems/d5fe3b3e-2054-4a62-a142-4d613b935097
-- title:
--   Idx: ord unit mul pow
-- statement:
--   The Idx construction uses the ord unit mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L115-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L115-L119

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

theorem Formalism.IrreducibleCountingLemmas.TW.Idx.ord_unit_mul_pow {ϖ : O} (hϖ : Irreducible ϖ) (u : Oˣ) (n : ℕ) :
    Ring.ord O ((u : O) * ϖ ^ n) = n := by sorry
