-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_ladder_sound
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.ladder_sound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:06.400913+00:00
-- url     : https://prove2.me/theorems/17921e65-1ee2-44ce-8546-e10a2d73a8d8
-- title:
--   Prime Counting Lemmas: ladder sound
-- statement:
--   The Prime Counting Lemmas construction uses the ladder sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean#L99-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean#L99-L115

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.ladder_sound {M F r T : ℕ} (hM : 0 < M) (hF : F = r.factorial) :
    ∀ (f a : ℕ), ladder M F r T f a = true →
    ∀ N, a ≤ N → N < T → (1 : ℝ) / 20 ≤ S N := by sorry
