-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wt_e3D_le
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.wt_e3D_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:07:30.893801+00:00
-- url     : https://prove2.me/theorems/d8c22e3d-e4d6-4356-9b80-746af4f373c3
-- title:
--   Galois Irreducibility: wt e3 D le
-- statement:
--   The Galois Irreducibility construction uses the wt e3 D le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L87-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L87-L100

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.wt_e3D_le (N : ℕ) (h : K[X]) (hm : h.Monic) :
    wtOf (e3μ K N) (e3D K N h) ≤ sqWeight h := by sorry
