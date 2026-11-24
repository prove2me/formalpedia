-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_gcd_mul_pow_totient
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.gcd_mul_pow_totient
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:44.764142+00:00
-- url     : https://prove2.me/theorems/7278c1b0-c1dd-4aec-9596-06ccdf594335
-- title:
--   Galois Irreducibility: gcd mul pow totient
-- statement:
--   The Galois Irreducibility construction uses the gcd mul pow totient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeToPartSpec.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeToPartSpec.lean#L9-L15

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.gcd_mul_pow_totient {q m : ℕ} (hm : 0 < m) (hcop : Nat.Coprime q m) :
    Nat.gcd (q * m) (q ^ Nat.totient m) = q := by sorry
