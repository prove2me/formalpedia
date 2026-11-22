-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_coeff
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:15.134887+00:00
-- url     : https://prove2.me/theorems/37cfc1e0-2529-4932-b9ac-d9e361403b87
-- title:
--   Galois Irreducibility: monic Of coeff
-- statement:
--   The Galois Irreducibility construction uses the monic Of coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRIrredCountUpper.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRIrredCountUpper.lean#L21-L30

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf_coeff (c : Fin N → K) (i : Fin N) : (monicOf c).coeff i = c i := by sorry
