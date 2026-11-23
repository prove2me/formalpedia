-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_primeToPart_eq_self_of_not_dvd
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart_eq_self_of_not_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:37.274612+00:00
-- url     : https://prove2.me/theorems/99cc387b-b179-4987-9470-8030a1dd6abd
-- title:
--   Galois Irreducibility: prime To Part eq self of not dvd
-- statement:
--   The Galois Irreducibility construction uses the prime To Part eq self of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L7-L12

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart_eq_self_of_not_dvd {M : Type} [Monoid M] {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0)
    {x : M} (hx : x ^ n = 1) (hln : ¬ l ∣ n) : primeToPart l x = x := by sorry
