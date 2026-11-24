-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_centralIdem_comm_of
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem_comm_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:22.703916+00:00
-- url     : https://prove2.me/theorems/ec480ecb-91c2-450c-b3f8-3c4070d2fb79
-- title:
--   Galois Irreducibility: central Idem comm of
-- statement:
--   The Galois Irreducibility construction uses the central Idem comm of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRCentralIdempotent.lean#L125-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRCentralIdempotent.lean#L125-L136

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem_comm_of {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (k : G) :
    centralIdem ρ * MonoidAlgebra.of ℂ G k = MonoidAlgebra.of ℂ G k * centralIdem ρ := by sorry
