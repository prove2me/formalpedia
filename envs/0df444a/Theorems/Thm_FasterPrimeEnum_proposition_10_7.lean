-- Prove2me | Theorems.Thm_FasterPrimeEnum_proposition_10_7
-- name    : FasterPrimeEnum.proposition_10_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:38:54.335657+00:00
-- url     : https://prove2.me/theorems/5587cdda-14f9-4819-b194-6661940b09c9
-- title:
--   Proposition 10.7 — the odd square-$Y$-rough integers below $N$ in time $O(N\log N/\log Y)$
-- statement:
--   Let $N$ and $Y$ be integers with $2\le Y\le N^{1/2}$. Given the bit array $(u_1,\dots,u_{N-1})$ of the $Y$-rough integers (the output of Theorem 10.1), a multitape Turing machine computes the sorted list of all odd square-$Y$-rough integers $n<N$ in time
--
--   $$
--   O\Big(\frac{N\log N}{\log Y}\Big).
--   $$
--
--   These integers contain every odd square-prime that is square-$Y$-rough, so counting them per interval bounds the odd square-primes of most intervals.
--
--   **Formalization Note** One machine and one constant before the input. The input is the framed triple of $N$, $Y$ (binary) and the bit array. The output is the increasing list, each element in binary, framed.
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) and RunsWithin (a halted run with exactly the output on a designated tape, within the time bound); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a constant factor is a shift of the exponent's o(1), or a change of the O-constant); an existential over the more restricted machine is the stronger statement
--   - reading: Let N and Y be as in Theorem 10.1. Given the output of Theorem 10.1 → input Encoding.encodeList id [binWord N, binWord Y, roughArray N Y]; reason: in Step 4 the algorithm knows N and Y; N is also the array's length plus one, and Y costs O(log N) bits, so supplying them changes no time bound
--   - encoding: a sorted list of integers → Encoding.encodeList binWord S with S strictly increasing; reason: standard binary, framed; the list is determined by its set and its order
--   - encoding: O(N log N / log Y) → one constant K before N, Y; reason: this is what the O / o(1) notation means for one algorithm (§1.1, p.1); the constants are chosen before every input
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Proposition 10.7, p.100

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_FasterPrimeEnum_IsRough

set_option autoImplicit false

namespace FasterPrimeEnum

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open Filter Topology

/-- **Proposition 10.7** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.100.

"Let N and Y be as in Theorem 10.1. Given the output of Theorem 10.1, we may compute a sorted list
of all odd square-Y-rough integers n < N in time O(N log N/log Y)."

**Formalization Note.** "As in Theorem 10.1" is `2 ⩽ Y`, `Y² ⩽ N`. The input is the framed triple
of `N`, `Y` (binary) and the bit array `roughArray N Y` of Theorem 10.1. The output is the
increasing list `S` of all odd square-`Y`-rough `n < N`, each in binary, framed; `S` is determined by
the two conditions. One machine and one constant before the input. At `N ⩾ 4` and `Y ⩾ 2` the
logarithms need no clipping. -/
theorem proposition_10_7 :
    ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (K : ℝ), 0 < K ∧
      ∀ N Y : ℕ, 2 ≤ Y → Y ^ 2 ≤ N →
        ∃ S : List ℕ, S.Pairwise (· < ·) ∧
          (∀ n, n ∈ S ↔ n < N ∧ n % 2 = 1 ∧ IsSquareRough (Y : ℝ) n) ∧
          RunsWithin A out (Encoding.encodeList id [binWord N, binWord Y, roughArray N Y])
            (Encoding.encodeList binWord S)
            (K * N * Real.log (N : ℝ) / Real.log (Y : ℝ)) := by sorry

end FasterPrimeEnum
