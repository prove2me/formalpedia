-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_e3A
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_e3A
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:58.982224+00:00
-- url     : https://prove2.me/theorems/27171fc3-1fe4-4cad-9d62-a0fde0c4de27
-- title:
--   Galois Irreducibility: mem e3 A
-- statement:
--   The Galois Irreducibility construction uses the mem e3 A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L68-L70

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_e3A {δ l : ℕ} {c : Fin δ → K} : c ∈ e3A K L δ l ↔ Irreducible (monicOf c) ∧
    ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L) := by sorry
