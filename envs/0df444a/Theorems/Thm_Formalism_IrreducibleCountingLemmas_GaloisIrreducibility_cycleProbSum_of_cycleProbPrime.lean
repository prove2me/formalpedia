-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_cycleProbSum_of_cycleProbPrime
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.cycleProbSum_of_cycleProbPrime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:23.425474+00:00
-- url     : https://prove2.me/theorems/f0cf1e3a-f310-4135-8894-c2dee99bf2d0
-- title:
--   Galois Irreducibility: cycle Prob Sum of cycle Prob Prime
-- statement:
--   The Galois Irreducibility construction uses the cycle Prob Sum of cycle Prob Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRJoints.lean#L7-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRJoints.lean#L7-L47

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRJoints
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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.cycleProbSum_of_cycleProbPrime : CycleProbPrime → CycleProbSum := by sorry
