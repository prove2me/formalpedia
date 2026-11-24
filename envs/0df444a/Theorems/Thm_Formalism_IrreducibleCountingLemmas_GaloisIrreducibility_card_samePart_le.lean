-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_samePart_le
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_samePart_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:26.243444+00:00
-- url     : https://prove2.me/theorems/50298d4e-72a7-4311-83b9-4378f6a024f4
-- title:
--   Galois Irreducibility: card same Part le
-- statement:
--   The Galois Irreducibility construction uses the card same Part le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CrossFactorCount.lean#L22-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CrossFactorCount.lean#L22-L47

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
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
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_samePart_le {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0) (w : L) (S : Finset L)
    (hS : ∀ x ∈ S, x ^ n = 1 ∧ primeToPart l x = w) : S.card ≤ l ^ padicValNat l n := by sorry
