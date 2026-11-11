-- Prove2me | Theorems.Thm_FasterPrimeEnum_proposition_7_13
-- name    : FasterPrimeEnum.proposition_7_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:38:57.004637+00:00
-- url     : https://prove2.me/theorems/4d04c4db-f82e-4b84-bc59-cee31eb587c7
-- title:
--   Proposition 7.13 — the primes from the odd square-primes in time $O(N)$
-- statement:
--   Let $N\ge2$. Given as input the sorted list of all odd square-primes $n<N$, a multitape Turing machine computes the sorted list of all primes $p<N$ in time
--
--   $$
--   O(N).
--   $$
--
--   This is the last step of every algorithm in the paper: after the odd square-primes are found, the primes are extracted by Möbius inversion at linear cost.
--
--   **Formalization Note** One machine and one constant before the input. The input is the framed pair of $N$ (binary) and the list. The output, the prime $2$ included, is in the format of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) and RunsWithin (a halted run with exactly the output on a designated tape, within the time bound); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a constant factor is a shift of the exponent's o(1), or a change of the O-constant); an existential over the more restricted machine is the stronger statement
--   - reading: Let N ⩾ 2. Given as input a sorted list of all odd square-primes n < N → input Encoding.encodeList id [binWord N, Encoding.encodeList binWord S]; reason: N is known to the algorithm and is not determined by the list; its binary word costs O(log N), so supplying it changes no time bound
--   - encoding: sorted lists of integers → Encoding.encodeList binWord of strictly increasing lists; reason: standard binary, framed
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Proposition 7.13, p.65

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_FasterPrimeEnum_primesBelow
import Definitions.Def_FasterPrimeEnum_IsSquarePrime

set_option autoImplicit false

namespace FasterPrimeEnum

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open Filter Topology

/-- **Proposition 7.13** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.65.

"Let N ⩾ 2. Given as input a sorted list of all odd square-primes n < N, we may compute a sorted
list of all primes p < N in time O(N)."

**Formalization Note.** One machine and one constant before the input. The input is the framed pair
of `N` (binary) and the increasing list of all odd square-primes `n < N` (each in binary, framed).
The output is the increasing list of all primes `p < N`, the prime `2` included, in the same format
as Theorem 1.2. -/
theorem proposition_7_13 :
    ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (K : ℝ), 0 < K ∧
      ∀ N : ℕ, 2 ≤ N → ∀ S : List ℕ, S.Pairwise (· < ·) →
        (∀ n, n ∈ S ↔ n < N ∧ n % 2 = 1 ∧ IsSquarePrime n) →
        RunsWithin A out (Encoding.encodeList id [binWord N, Encoding.encodeList binWord S])
          (Encoding.encodeList binWord (primesBelow N)) (K * N) := by sorry

end FasterPrimeEnum
