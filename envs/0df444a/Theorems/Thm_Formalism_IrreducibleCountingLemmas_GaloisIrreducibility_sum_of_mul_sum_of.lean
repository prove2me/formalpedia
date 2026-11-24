-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sum_of_mul_sum_of
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sum_of_mul_sum_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:56.580653+00:00
-- url     : https://prove2.me/theorems/0f00d417-be07-44a3-b4cc-57aea728b7f5
-- title:
--   Galois Irreducibility: sum of mul sum of
-- statement:
--   The Galois Irreducibility construction uses the sum of mul sum of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRCentralIdempotent.lean#L71-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRCentralIdempotent.lean#L71-L81

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sum_of_mul_sum_of (A B : G → ℂ) :
    (∑ g, A g • MonoidAlgebra.of ℂ G g) * (∑ g, B g • MonoidAlgebra.of ℂ G g) =
      ∑ k, (∑ g, A g * B (g⁻¹ * k)) • MonoidAlgebra.of ℂ G k := by sorry
