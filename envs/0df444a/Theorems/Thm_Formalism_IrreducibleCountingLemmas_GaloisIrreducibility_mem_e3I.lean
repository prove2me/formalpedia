-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_e3I
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_e3I
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:13.154261+00:00
-- url     : https://prove2.me/theorems/dbcb75d9-1ddc-49d0-afcf-4abcf9e3ba53
-- title:
--   Galois Irreducibility: mem e3 I
-- statement:
--   The Galois Irreducibility construction uses the mem e3 I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L73-L75

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
variable {K}

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_e3I {δ : ℕ} {c : Fin δ → K} : c ∈ e3I K δ ↔ Irreducible (monicOf c) ∧
    (monicOf c).coeff 0 ≠ 0 := by sorry
