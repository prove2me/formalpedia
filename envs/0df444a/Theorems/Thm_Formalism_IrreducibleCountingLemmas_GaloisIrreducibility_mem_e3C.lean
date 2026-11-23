-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_e3C
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_e3C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:31.807541+00:00
-- url     : https://prove2.me/theorems/34147f7b-ae59-47ae-8ba8-f8b53b3a6a6e
-- title:
--   Galois Irreducibility: mem e3 C
-- statement:
--   The Galois Irreducibility construction uses the mem e3 C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L78-L81

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_e3C {δ l : ℕ} {P' : K[X]} {c : Fin δ → K} : c ∈ e3C K L δ l P' ↔
    Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 ∧ ∃ x ∈ (monicOf c).rootSet L,
      ∃ y ∈ P'.rootSet L, primeToPart l x = primeToPart l y := by sorry
