-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mono_not_adm
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mono_not_adm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:15.111105+00:00
-- url     : https://prove2.me/theorems/c15228bf-3657-476b-9c53-56a0559ac045
-- title:
--   Galois Irreducibility: mono not adm
-- statement:
--   The Galois Irreducibility construction uses the mono not adm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L899-L958
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L899-L958

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mono_not_adm (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (n : GL (Fin N) K)
    (π : Equiv.Perm (Fin N)) (t : Fin N → K) (ht : ∀ j, t j ≠ 0)
    (hn : ∀ i j, (n : Matrix (Fin N) (Fin N) K) i j = if i = π j then t j else 0)
    (hadm : ¬ MonoAdm π t) :
    ∃ u u' : uniSub K N, (u : GL (Fin N) K) * n * u' = n ∧
      uniChar ψ₀ N u * uniChar ψ₀ N u' ≠ 1 := by sorry
