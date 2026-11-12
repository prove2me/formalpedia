-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_corollary_3_11
-- name    : CatalyticTreeEval.Main.corollary_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:16.238862+00:00
-- url     : https://prove2.me/theorems/4336e408-913c-45bc-9929-3dd475c928f9
-- title:
--   Corollary 3.11 — exact-size uniform families in both regimes
-- statement:
--   Both assertions hold, with family size exactly $2^\ell$.
--
--   1. Fix $t\ge2$ distinct odd primes, with product $m$. One finite printer and positive constants, depending only on those fixed primes, work for every $\ell\ge1$. The canonical-set matching family has dimension
--
--   $$d\le2^{C_d\ell^{1/t}(\log_2(\ell+2))^{1-1/t}}.$$
--
--   2. There are one finite printer, positive absolute constants and an absolute integer threshold $L\ge2$ such that for every $\ell\ge L$, with $t=\lceil\sqrt{\log_2\ell}\rceil$ and $m$ the product of the first $t$ odd primes, the canonical-set matching family has dimension
--
--   $$d\le2^{2^{C_d\sqrt{\log_2\ell}}}.$$
--
--   In each case the printer uses at most $C_s(\ell+\operatorname{lg}d+\operatorname{lg}m)$ work bits, where $\operatorname{lg}a=1+\log_2(a+1)$. Both clauses are retained even though only the first is needed for Corollary 4.7. The dimension bounds do not replace the exact-size or uniform-printing claims.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
--   - encoding: log-space uniformity O(log N+log d+log m) → N=2^ℓ and positive shifted logarithms lg d, lg m; reason: these are equivalent uniform logarithmic bounds; the second regime has one absolute threshold and the first has no cutoff
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Corollary 3.11, printed p. 17 (PDF p. 19); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Matching

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- Both numbered regimes of Corollary 3.11, printed p.17 / PDF p.19. -/
theorem corollary_3_11 :
    (∀ (t : ℕ) (p : Fin t → ℕ), 2 ≤ t → OddPrimeData p →
      ∃ (M : Machine) (Cd Cs : ℝ), 0 < Cd ∧ 0 < Cs ∧
        ∀ l : ℕ, 1 ≤ l →
        ∃ (d : ℕ) (U V : Fin (2 ^ l) → Vec (modulus p) d),
          (d : ℝ) ≤ exp₂ (Cd * (l : ℝ) ^ (1 / (t : ℝ)) *
            (log₂ (l + 2)) ^ (1 - 1 / (t : ℝ))) ∧
          SMatching (canonical p (modulus p)) U V ∧
          VectorAccess M (natCode l) U V (Cs * (l + lg d + lg (modulus p)))) ∧
    (∃ (M : Machine) (Cd Cs : ℝ) (L : ℕ), 0 < Cd ∧ 0 < Cs ∧ 2 ≤ L ∧
      ∀ l : ℕ, L ≤ l →
      ∃ (d : ℕ) (U V : Fin (2 ^ l) → Vec (modulus (firstOddPrimes (variablePrimeCount l))) d),
        (d : ℝ) ≤ exp₂ (exp₂ (Cd * Real.sqrt (log₂ l))) ∧
        SMatching (canonical (firstOddPrimes (variablePrimeCount l))
          (modulus (firstOddPrimes (variablePrimeCount l)))) U V ∧
        VectorAccess M (natCode l) U V
          (Cs * (l + lg d + lg (modulus (firstOddPrimes (variablePrimeCount l)))))) := by sorry

end CatalyticTreeEval.Main
