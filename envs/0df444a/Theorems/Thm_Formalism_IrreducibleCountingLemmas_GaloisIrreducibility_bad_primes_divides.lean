-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_bad_primes_divides
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bad_primes_divides
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:39.348386+00:00
-- url     : https://prove2.me/theorems/d382a3aa-d79b-462e-b56f-56a5b022501d
-- title:
--   Galois Irreducibility: bad primes divides
-- statement:
--   The Galois Irreducibility construction uses the bad primes divides property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRBBDivides.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRBBDivides.lean#L7-L17

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBDivides
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.GaloisIrreducibility (IsSubSum IsOrbit)

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bad_primes_divides : BBDivides := by sorry
