-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_primeCounting_le
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.primeCounting_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:37.351824+00:00
-- url     : https://prove2.me/theorems/b6f75278-102a-42ff-9531-fe9825cb4e06
-- title:
--   Prime Counting Lemmas: prime Counting le
-- statement:
--   The Prime Counting Lemmas construction uses the prime Counting le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean#L186-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean#L186-L198

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.primeCounting_le (s : ℕ) (hs : 6 ≤ s) : (primeCounting s : ℝ) ≤ s / 3 + 3 := by sorry
