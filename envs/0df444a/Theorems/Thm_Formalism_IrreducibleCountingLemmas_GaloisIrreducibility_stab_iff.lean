-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_stab_iff
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.stab_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:02.496582+00:00
-- url     : https://prove2.me/theorems/d7292a6c-4670-4a92-b6cb-1dfdbb58c517
-- title:
--   Galois Irreducibility: stab iff
-- statement:
--   The Galois Irreducibility construction uses the stab iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRLemmaP.lean#L47-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRLemmaP.lean#L47-L60

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
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
variable {N : ℕ}

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.stab_iff (A : Finset (Fin N)) (σ : Equiv.Perm (Fin N)) (h : ∀ x ∈ A, σ x ∈ A) (x : Fin N) :
    σ x ∈ A ↔ x ∈ A := by sorry
