-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_chk_sound
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.chk_sound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:34.288767+00:00
-- url     : https://prove2.me/theorems/f16995be-088b-4c71-8487-245ee8ee94f3
-- title:
--   Prime Counting Lemmas: chk sound
-- statement:
--   The Prime Counting Lemmas construction uses the chk sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean#L61-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean#L61-L93

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.chk_sound {M F r a b : ℕ} (hM : 0 < M) (hF : F = r.factorial)
    (h : chk M F r a b = true) (N : ℕ)
    (haN : a ≤ N) (hNb : N ≤ b) : (1 : ℝ) / 20 ≤ S N := by sorry
