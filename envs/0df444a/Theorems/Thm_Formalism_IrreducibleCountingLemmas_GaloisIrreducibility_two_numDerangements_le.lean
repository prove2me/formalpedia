-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_two_numDerangements_le
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.two_numDerangements_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:11.144645+00:00
-- url     : https://prove2.me/theorems/835df9b8-f633-44a0-be93-6195ff45c3bf
-- title:
--   Galois Irreducibility: two num Derangements le
-- statement:
--   The Galois Irreducibility construction uses the two num Derangements le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRLemmaP.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRLemmaP.lean#L7-L19

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.two_numDerangements_le (n : ℕ) (hn : 1 ≤ n) : 2 * numDerangements n ≤ n.factorial := by sorry
