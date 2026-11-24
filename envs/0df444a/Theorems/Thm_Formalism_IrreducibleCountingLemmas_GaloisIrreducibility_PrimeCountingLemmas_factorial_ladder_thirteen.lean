-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_factorial_ladder_thirteen
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.factorial_ladder_thirteen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:49.768379+00:00
-- url     : https://prove2.me/theorems/446c3c60-a9f9-47f0-af48-e319f46a8c0d
-- title:
--   Prime Counting Lemmas: factorial ladder thirteen
-- statement:
--   The Prime Counting Lemmas construction uses the factorial ladder thirteen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean#L117-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean#L117-L117

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.factorial_ladder_thirteen : ladder 1000000000 (Nat.factorial 13) 13 196 60 100 = true := by sorry
