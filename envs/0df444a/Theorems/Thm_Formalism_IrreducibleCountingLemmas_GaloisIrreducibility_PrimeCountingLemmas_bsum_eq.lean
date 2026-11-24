-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_bsum_eq
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.bsum_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:03.589301+00:00
-- url     : https://prove2.me/theorems/496c506e-3c4a-4a98-934e-d9723808b7d7
-- title:
--   Prime Counting Lemmas: bsum eq
-- statement:
--   The Prime Counting Lemmas construction uses the bsum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean#L47-L56

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Nat
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.bsum_eq (t : ℕ → ℕ) : ∀ k lo, bsum t k lo = ∑ p ∈ Finset.Ico lo (lo + 2 ^ k), t p := by sorry
