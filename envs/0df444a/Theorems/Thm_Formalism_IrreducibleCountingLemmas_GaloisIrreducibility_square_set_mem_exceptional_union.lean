-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_square_set_mem_exceptional_union
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.square_set_mem_exceptional_union
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:22.901812+00:00
-- url     : https://prove2.me/theorems/c9c907f4-7a1d-4ba9-afa0-dccb0662fc8d
-- title:
--   Galois Irreducibility: square set mem exceptional union
-- statement:
--   The Galois Irreducibility construction uses the square set mem exceptional union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L276-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L276-L347

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
variable {K L}

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.square_set_mem_exceptional_union {N : ℕ} {c : Fin N → K} (hc : c ∈ sqSet K N) {l : ℕ} (hl : l.Prime)
    (hlBB : l ∉ BB (Fintype.card K) N)
    (hninj : ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L)) :
    c ∈ e3SA K L N ∪ e3SB K L N := by sorry
