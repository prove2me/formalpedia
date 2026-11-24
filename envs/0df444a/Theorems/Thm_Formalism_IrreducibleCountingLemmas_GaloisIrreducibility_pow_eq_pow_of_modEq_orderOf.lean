-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_pow_eq_pow_of_modEq_orderOf
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.pow_eq_pow_of_modEq_orderOf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:58.343798+00:00
-- url     : https://prove2.me/theorems/64280b49-56f9-4c8d-8d20-20a3c84d430e
-- title:
--   Galois Irreducibility: pow eq pow of mod Eq order Of
-- statement:
--   The Galois Irreducibility construction uses the pow eq pow of mod Eq order Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeToPartSpec.lean#L5-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeToPartSpec.lean#L5-L7

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.pow_eq_pow_of_modEq_orderOf {M : Type*} [Monoid M] (x : M) {a b : ℕ}
    (h : a ≡ b [MOD orderOf x]) : x ^ a = x ^ b := by sorry
