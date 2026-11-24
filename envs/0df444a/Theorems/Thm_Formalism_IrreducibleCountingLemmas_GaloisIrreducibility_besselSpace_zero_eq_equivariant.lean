-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_besselSpace_zero_eq_equivariant
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace_zero_eq_equivariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:31.65632+00:00
-- url     : https://prove2.me/theorems/6b2e426d-66a5-401a-af41-061084bf9101
-- title:
--   Galois Irreducibility: bessel Space zero eq equivariant
-- statement:
--   The Galois Irreducibility construction uses the bessel Space zero eq equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L281-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L281-L297

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace_zero_eq_equivariant {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) K) V) (ψ₀ : AddChar K ℂ) :
    besselSpace ρ ψ₀ 0 0 = eqvSpace ρ (fun u : uniSub K N => (u : GL (Fin N) K))
      (fun u => ((uniChar ψ₀ N u : ℂˣ) : ℂ)) := by sorry
