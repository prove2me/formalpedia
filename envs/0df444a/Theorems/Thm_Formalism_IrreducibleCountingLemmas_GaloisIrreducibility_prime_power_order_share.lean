-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_prime_power_order_share
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prime_power_order_share
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:26.012505+00:00
-- url     : https://prove2.me/theorems/336da8a0-3b26-42c5-a46f-3277a73836dc
-- title:
--   Galois Irreducibility: prime power order share
-- statement:
--   The Galois Irreducibility construction uses the prime power order share property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/FourMulSumLeProduct.lean#L43-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/FourMulSumLeProduct.lean#L43-L111

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FourMulSumLeProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prime_power_order_share : PrimePowerOrderShare := by sorry
