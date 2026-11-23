-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_pow_sub_one_pos
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_pow_sub_one_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:24.041627+00:00
-- url     : https://prove2.me/theorems/d25c9938-2d18-4a21-9412-5147ebc45493
-- title:
--   Galois Irreducibility: card pow sub one pos
-- statement:
--   The Galois Irreducibility construction uses the card pow sub one pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L102-L105

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_pow_sub_one_pos (δ : ℕ) (hδ : 1 ≤ δ) : (0 : ℝ) < (Fintype.card K : ℝ) ^ δ - 1 := by sorry
