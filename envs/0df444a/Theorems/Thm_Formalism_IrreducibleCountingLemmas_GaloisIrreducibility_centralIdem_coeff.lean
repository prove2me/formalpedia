-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_centralIdem_coeff
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem_coeff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:25.315449+00:00
-- url     : https://prove2.me/theorems/f7c7d945-f291-438a-afe4-95a26c5973df
-- title:
--   Galois Irreducibility: central Idem coeff
-- statement:
--   The Galois Irreducibility construction uses the central Idem coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRCentralIdemSelfAdjoint.lean#L68-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRCentralIdemSelfAdjoint.lean#L68-L79

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem_coeff {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (x : G) :
    (centralIdem ρ).coeff x =
      (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ρ.character x⁻¹ := by sorry
