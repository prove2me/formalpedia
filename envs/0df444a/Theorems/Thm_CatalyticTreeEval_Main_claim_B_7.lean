-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_claim_B_7
-- name    : CatalyticTreeEval.Main.claim_B_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:31.420744+00:00
-- url     : https://prove2.me/theorems/b82057ab-4488-4080-944b-02a5d950c6ec
-- title:
--   Claim B.7 — space-bounded subset indexing
-- statement:
--   For every $H\ge w\ge1$, set $N=\binom Hw$. There is a bijection from $\{0,\ldots,N-1\}$ to the subsets of $\{0,\ldots,H-1\}$ of size $w$. One finite machine, with a positive absolute constant independent of $H,w$ and the index, prints the subset corresponding to any supplied index using
--
--   $$C(1+\log_2N+\log_2H)$$
--
--   work bits, rounded upward. Subsets are printed as their increasing lists of elements. The entire bijection is surjective and injective, rather than merely providing a subset for each index. This indexes the matching-family members uniformly, including the singleton range when $H=w$.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
--   - encoding: indices in [N] and [H]; space O(log N+log H) → zero-based indices and the bound C(1+log₂ N+log₂ H); reason: translation by one is a bijection; the additive unit covers H=w=1 where both logarithms vanish
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Claim B.7, printed p. 38 (PDF p. 40); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Polynomials

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem claim_B_7 :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ (H w : ℕ), 1 ≤ w → w ≤ H →
      ∃ e : Fin (H.choose w) ≃ {T : Finset (Fin H) // T.card = w},
        ∀ i, Prints M (natsCode [H,w,i.val])
          (natsCode (((List.finRange H).filter fun j => j ∈ (e i).val).map Fin.val))
          (C * (1 + log₂ (H.choose w) + log₂ H)) := by sorry

end CatalyticTreeEval.Main
