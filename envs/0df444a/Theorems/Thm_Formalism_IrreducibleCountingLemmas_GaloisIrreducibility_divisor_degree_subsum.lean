-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_divisor_degree_subsum
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.divisor_degree_subsum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:26.828798+00:00
-- url     : https://prove2.me/theorems/4d26a18f-d970-42c5-aba5-d0007ca4bcfb
-- title:
--   Galois Irreducibility: divisor degree subsum
-- statement:
--   The Galois Irreducibility construction uses the divisor degree subsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRDivisorDegreeSubSum.lean#L14-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRDivisorDegreeSubSum.lean#L14-L34

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Lemmata_GeneralBFactRightRest_Imports
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial UniqueFactorizationMonoid
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.GaloisIrreducibility (IsSubSum)

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.divisor_degree_subsum : DivisorDegreeSubSum := by sorry
