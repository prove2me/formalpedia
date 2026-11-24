-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_besselChar_zero_eq_edge_sum
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselChar_zero_eq_edge_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:26.725505+00:00
-- url     : https://prove2.me/theorems/02c47323-ab8e-4341-a471-832fefa10fa1
-- title:
--   Galois Irreducibility: bessel Char zero eq edge sum
-- statement:
--   The Galois Irreducibility construction uses the bessel Char zero eq edge sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L196-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L196-L204

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselChar_zero_eq_edge_sum (ψ₀ : AddChar K ℂ) (u : GL (Fin N) K) :
    besselChar ψ₀ 0 0 N u = ψ₀ (edgeSum (u : Matrix (Fin N) (Fin N) K)) := by sorry
