-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_injective
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:45.64656+00:00
-- url     : https://prove2.me/theorems/d0c09b0b-cc4d-40fa-b72c-e9d3535cf5f3
-- title:
--   Galois Irreducibility: monic Of injective
-- statement:
--   The Galois Irreducibility construction uses the monic Of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRIrredCountUpper.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRIrredCountUpper.lean#L32-L35

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf_injective : Function.Injective (monicOf : (Fin N → K) → K[X]) := by sorry
