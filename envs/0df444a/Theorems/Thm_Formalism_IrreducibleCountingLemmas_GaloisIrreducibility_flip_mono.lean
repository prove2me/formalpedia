-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_flip_mono
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.flip_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:55.532681+00:00
-- url     : https://prove2.me/theorems/ba8bcc38-024e-4067-9ac1-b60c15f63aae
-- title:
--   Galois Irreducibility: flip mono
-- statement:
--   The Galois Irreducibility construction uses the flip mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L867-L897
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L867-L897

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K : Type} [Field K] {N : ℕ}

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.flip_mono (n : GL (Fin N) K) (π : Equiv.Perm (Fin N)) (t : Fin N → K)
    (hn : ∀ i j, (n : Matrix (Fin N) (Fin N) K) i j = if i = π j then t j else 0)
    (hadm : MonoAdm π t) : flipG n = n := by sorry
