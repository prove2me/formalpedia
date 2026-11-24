-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_exists_prime_pow_eq
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.exists_prime_pow_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:15.991915+00:00
-- url     : https://prove2.me/theorems/62a29dca-ebf1-4f99-a8f3-cb4325ea599f
-- title:
--   E4: exists prime pow eq
-- statement:
--   The E4 construction uses the exists prime pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L116-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean#L116-L134

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ProdPowFactorizationLe
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FourMulSumLeProduct
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateThird
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
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.exists_prime_pow_eq {M : Type} [Monoid M] (n : ℕ) (hn : 2 ≤ n) (u : M) (hu : u ^ n = 1)
    (l a : ℕ) (hl : l.Prime) (hla : u ^ (l ^ a) = 1) :
    ∃ l' ∈ n.primeFactors, u ^ (l' ^ padicValNat l' n) = 1 := by sorry
