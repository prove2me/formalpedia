-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mul_elM
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mul_elM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:35.711869+00:00
-- url     : https://prove2.me/theorems/6b089782-228e-48bf-963e-49aa1eee479f
-- title:
--   Galois Irreducibility: mul el M
-- statement:
--   The Galois Irreducibility construction uses the mul el M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L828-L834
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L828-L834

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mul_elM (p q : Fin N) (v : K) (h : Matrix (Fin N) (Fin N) K) (x c : Fin N) :
    (h * elM p q v) x c = h x c + if c = q then h x p * v else 0 := by sorry
