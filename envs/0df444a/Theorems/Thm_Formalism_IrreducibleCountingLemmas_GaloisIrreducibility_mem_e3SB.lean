-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_e3SB
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_e3SB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:48.291268+00:00
-- url     : https://prove2.me/theorems/f61cf998-f556-4e49-86dd-08d778a001fa
-- title:
--   Galois Irreducibility: mem e3 SB
-- statement:
--   The Galois Irreducibility construction uses the mem e3 SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L235-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L235-L274

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_e3SB {N : ℕ} {c : Fin N → K} (hc : c ∈ sqSet K N) {l : ℕ} (hl : l.Prime)
    (hcond : ∀ d ∈ Finset.Icc 1 N,
      l ^ (4 * padicValNat l (Fintype.card K ^ d - 1)) ≤ Fintype.card K ^ d)
    {δ δ' : ℕ} (hδ' : 1 ≤ δ') (hδδ' : δ' ≤ δ) (hδN : δ ≤ N) {c' : Fin δ → K} {c'' : Fin δ' → K}
    (hi' : Irreducible (monicOf c')) (hi'' : Irreducible (monicOf c''))
    (h0' : (monicOf c').coeff 0 ≠ 0) (h0'' : (monicOf c'').coeff 0 ≠ 0)
    (hd' : monicOf c' ∣ monicOf c) (hd'' : monicOf c'' ∣ monicOf c) {x y : L}
    (hx : aeval x (monicOf c') = 0) (hy : aeval y (monicOf c'') = 0)
    (hxy : primeToPart l x = primeToPart l y) (hne : x ≠ y)
    (hPne : monicOf c' ≠ monicOf c'') : c ∈ e3SB K L N := by sorry
