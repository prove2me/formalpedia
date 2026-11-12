-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_theorem_3_10
-- name    : CatalyticTreeEval.Main.theorem_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:21.708198+00:00
-- url     : https://prove2.me/theorems/30550d35-f356-4a73-a137-18e705db06a9
-- title:
--   Theorem 3.10 — matching vectors with a dimension bound
-- statement:
--   Let $t\ge1$, let $p_1,\ldots,p_t$ be distinct primes supplied as input, let $m=\prod_i p_i$, and let $H\ge w\ge1$. Put $N=\binom Hw$ and $r=(mw)^{1/t}$. There is a canonical-set matching-vector family of size $N$ whose dimension satisfies
--
--   $$d\le\sum_{j=0}^{\lfloor r\rfloor}\binom Hj.$$
--
--   One finite printer, uniform over all these parameters, prints the requested pair of vectors using at most $C(1+\log_2N+r\log_2(H+1)+\log_2m)$ work bits, with one positive absolute constant. The upper summation endpoint is inclusive. This combines the prime-power construction with the paper's parameter choice and retains its uniformity clause.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
--   - encoding: O(log N+(mw)^(1/t) log(H+1)+log m) → the same formula with an additive one and a sum over range(floor(r)+1); reason: m>1 absorbs the unit; the finite range includes the displayed endpoint
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Theorem 3.10, printed p. 16 (PDF p. 18); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Polynomials

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem theorem_3_10 :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ (t : ℕ) (p : Fin t → ℕ) (w H : ℕ),
      PrimeData p → 1 ≤ w → w ≤ H →
      ∃ (d : ℕ) (U V : Fin (H.choose w) → Vec (modulus p) d),
        d ≤ binomialDimension H (⌊((modulus p * w : ℕ) : ℝ) ^ (1 / (t : ℝ))⌋₊ + 1) ∧
        SMatching (canonical p (modulus p)) U V ∧
        VectorAccess M (primeCode p ++ natsCode [w,H]) U V
          (C * (1 + log₂ (H.choose w) +
            ((modulus p * w : ℕ) : ℝ) ^ (1 / (t : ℝ)) * log₂ (H + 1) + log₂ (modulus p))) := by sorry

end CatalyticTreeEval.Main
