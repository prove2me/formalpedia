-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_pow_lpow_add
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.pow_lpow_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:48.331817+00:00
-- url     : https://prove2.me/theorems/191c3750-e3da-4a4b-8a1b-d693571be254
-- title:
--   Galois Irreducibility: pow lpow add
-- statement:
--   The Galois Irreducibility construction uses the pow lpow add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeToPartEqIff.lean#L5-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeToPartEqIff.lean#L5-L7

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.pow_lpow_add {M : Type*} [Monoid M] {l a : ℕ} {x z : M} (h : x ^ (l ^ a) = z ^ (l ^ a))
    (b : ℕ) : x ^ (l ^ (a + b)) = z ^ (l ^ (a + b)) := by sorry
