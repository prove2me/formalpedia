-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_mult_le
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_mult_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:13.494602+00:00
-- url     : https://prove2.me/theorems/dd1f04d2-d82d-46a5-8324-9f7b2b0de02c
-- title:
--   Galois Irreducibility: card mult le
-- statement:
--   The Galois Irreducibility construction uses the card mult le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRSquarefreeCount.lean#L9-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRSquarefreeCount.lean#L9-L37

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Classical

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_mult_le {K : Type} [Field K] [Fintype K] (N j : ℕ) (P : K[X]) (hP : P.Monic)
    (hj : P.natDegree = j) :
    ((Finset.univ : Finset (Fin N → K)).filter (fun c => P * P ∣ monicOf c)).card
      ≤ Fintype.card K ^ (N - 2 * j) := by sorry
