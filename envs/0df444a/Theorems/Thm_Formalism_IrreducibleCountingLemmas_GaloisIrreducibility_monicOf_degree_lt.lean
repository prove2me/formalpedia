-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_degree_lt
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf_degree_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:43.425691+00:00
-- url     : https://prove2.me/theorems/5f00997b-495b-4c3c-a846-355e58254db0
-- title:
--   Galois Irreducibility: monic Of degree lt
-- statement:
--   The Galois Irreducibility construction uses the monic Of degree lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRIrredCountUpper.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRIrredCountUpper.lean#L9-L10

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
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
variable {K : Type} [Field K] {N : ℕ}

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf_degree_lt (c : Fin N → K) :
    (∑ i : Fin N, C (c i) * X ^ (i : ℕ)).degree < (N : WithBot ℕ) := by sorry
