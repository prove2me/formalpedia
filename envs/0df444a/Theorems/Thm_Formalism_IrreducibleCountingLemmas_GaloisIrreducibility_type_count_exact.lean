-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_type_count_exact
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.type_count_exact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:08.168671+00:00
-- url     : https://prove2.me/theorems/aedf7f3d-aa6d-49bc-88ab-782a5eded323
-- title:
--   Galois Irreducibility: type count exact
-- statement:
--   The Galois Irreducibility construction uses the type count exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRTypeCountExact.lean#L9-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRTypeCountExact.lean#L9-L226

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
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
set_option maxHeartbeats 800000

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.type_count_exact : TypeCountExact := by sorry
