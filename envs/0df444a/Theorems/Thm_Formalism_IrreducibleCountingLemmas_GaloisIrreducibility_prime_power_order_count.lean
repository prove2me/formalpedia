-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_prime_power_order_count
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prime_power_order_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:50.269797+00:00
-- url     : https://prove2.me/theorems/47937923-fdca-4812-9a51-4bc57e2cea6e
-- title:
--   Galois Irreducibility: prime power order count
-- statement:
--   The Galois Irreducibility construction uses the prime power order count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ProdPowFactorizationLe.lean#L73-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ProdPowFactorizationLe.lean#L73-L128

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ProdPowFactorizationLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prime_power_order_count : PrimePowerOrderCount := by sorry
