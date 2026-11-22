-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_sIdx_eq_sub
-- name    : Formalism.IrreducibleCountingLemmas.TW.Idx.sIdx_eq_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:12.581402+00:00
-- url     : https://prove2.me/theorems/7b4de9ee-6db6-49e3-9569-58a25b49d32f
-- title:
--   Idx: s Idx eq sub
-- statement:
--   The Idx construction uses the s Idx eq sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L204-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L204-L218

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

theorem Formalism.IrreducibleCountingLemmas.TW.Idx.sIdx_eq_sub {M N Q : Submodule O V} (hM : IsLat O K M) (hN : IsLat O K N)
    (hQ : IsLat O K Q) (hQM : Q ≤ M) (hQN : Q ≤ N) :
    sIdx M N = ((relLen M Q).toNat : ℤ) - ((relLen N Q).toNat : ℤ) := by sorry
