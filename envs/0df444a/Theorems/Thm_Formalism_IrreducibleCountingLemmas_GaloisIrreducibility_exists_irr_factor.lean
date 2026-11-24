-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_exists_irr_factor
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_irr_factor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:59.902559+00:00
-- url     : https://prove2.me/theorems/ded19137-fee2-43bd-9bb0-5161f868be7e
-- title:
--   Galois Irreducibility: exists irr factor
-- statement:
--   The Galois Irreducibility construction uses the exists irr factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L194-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L194-L205

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_irr_factor {f : K[X]} (hf : f ≠ 0) (h0 : f.coeff 0 ≠ 0) {x : L}
    (hx : aeval x f = 0) :
    ∃ δ, 1 ≤ δ ∧ δ ≤ f.natDegree ∧ ∃ c' : Fin δ → K, Irreducible (monicOf c') ∧
      (monicOf c').coeff 0 ≠ 0 ∧ monicOf c' ∣ f ∧ aeval x (monicOf c') = 0 := by sorry
