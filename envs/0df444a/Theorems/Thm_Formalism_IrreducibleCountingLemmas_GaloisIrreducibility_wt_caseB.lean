-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wt_caseB
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.wt_caseB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:48.311312+00:00
-- url     : https://prove2.me/theorems/95b6e490-b7e4-48c5-9aad-a0a1303636a2
-- title:
--   Galois Irreducibility: wt case B
-- statement:
--   The Galois Irreducibility construction uses the wt case B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L125-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L125-L177

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.wt_caseB (N δ δ' l : ℕ) (hl : l.Prime) (hδ : 1 ≤ δ) (hδ' : 1 ≤ δ')
    (hBB : l ^ (4 * padicValNat l (Fintype.card K ^ δ - 1)) ≤ Fintype.card K ^ δ) :
    wtOf (e3μ K N) (⋃ c'' ∈ e3I K δ', ⋃ c' ∈ e3C K L δ l (monicOf c''),
        e3D K N (monicOf c' * monicOf c'')) ≤
      (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by sorry
