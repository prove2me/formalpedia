-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_prime_cycle_probability
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prime_cycle_probability
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:50.291318+00:00
-- url     : https://prove2.me/theorems/559f3bf3-208e-44bf-8b4e-9a4fc6387e9b
-- title:
--   Galois Irreducibility: prime cycle probability
-- statement:
--   The Galois Irreducibility construction uses the prime cycle probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRCycleProbPrime.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRCycleProbPrime.lean#L113-L115

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Equiv Equiv.Perm Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prime_cycle_probability : CycleProbPrime := by sorry
