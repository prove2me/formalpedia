-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_div_fourth_sub_one_le
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.div_fourth_sub_one_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:03.942804+00:00
-- url     : https://prove2.me/theorems/c7fd7880-3298-4e3f-a079-5d3b39476fe6
-- title:
--   Galois Irreducibility: div fourth sub one le
-- statement:
--   The Galois Irreducibility construction uses the div fourth sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L362-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L362-L372

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.div_fourth_sub_one_le (s : ℝ) (hs : 2 ≤ s) : s * (s ^ 4 - 1)⁻¹ ≤ 2 * (1 / s ^ 3) := by sorry
