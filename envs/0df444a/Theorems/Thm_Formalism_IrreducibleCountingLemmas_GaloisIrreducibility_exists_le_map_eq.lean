-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_exists_le_map_eq
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_le_map_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:34.995422+00:00
-- url     : https://prove2.me/theorems/a23fbd2a-f5e3-45d3-bae4-474aaf0ca963
-- title:
--   Galois Irreducibility: exists le map eq
-- statement:
--   The Galois Irreducibility construction uses the exists le map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRDivisorDegreeSubSum.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRDivisorDegreeSubSum.lean#L10-L12

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_le_map_eq {α β : Type*} [DecidableEq β] (f : α → β) (t : Multiset α) :
    ∀ s : Multiset β, s ≤ t.map f → ∃ u ≤ t, u.map f = s := by sorry
