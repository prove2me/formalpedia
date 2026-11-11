-- Prove2me | Theorems.Thm_FasterPrimeEnum_theorem_10_1
-- name    : FasterPrimeEnum.theorem_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:38:53.32678+00:00
-- url     : https://prove2.me/theorems/fae1d909-d333-41fd-9133-f4809e5f7c4a
-- title:
--   Theorem 10.1 — the $Y$-rough integers below $N$ in time $O(N\log Y)$
-- statement:
--   There is a deterministic algorithm, a multitape Turing machine, with the following properties. It takes as input positive integers $N$ and $Y$ with $2\le Y\le N^{1/2}$. Its output is a bit array $(u_1,\dots,u_{N-1})$ with $u_n=1$ if and only if $n$ is $Y$-rough. Its running time is
--
--   $$
--   O(N\log Y).
--   $$
--
--   This generalizes Sergeev's $O(N\log N)$ prime sieve; stopped at $Y=\exp(40(\log N)^{1/2}\log\log N)$ it is cheap enough for the deterministic algorithm and still identifies almost all intervals as unproblematic.
--
--   **Formalization Note** One machine, one output tape and one constant before the input. The input is the framed pair of the binary words of $N$ and $Y$; for integers, $Y\le N^{1/2}$ is $Y^2\le N$. The output is the list $u_1,\dots,u_{N-1}$.
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) and RunsWithin (a halted run with exactly the output on a designated tape, within the time bound); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a constant factor is a shift of the exponent's o(1), or a change of the O-constant); an existential over the more restricted machine is the stronger statement
--   - encoding: input positive integers N, Y; output a bit array (u_1, …, u_{N−1}) → input Encoding.encodeList id [binWord N, binWord Y]; output the list [u_1, …, u_{N−1}] of Bool; reason: the paper fixes no tape layout
--   - encoding: O(N log Y) → one constant K before N, Y; reason: this is what the O / o(1) notation means for one algorithm (§1.1, p.1); the constants are chosen before every input
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Theorem 10.1, p.95

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_FasterPrimeEnum_IsRough

set_option autoImplicit false

namespace FasterPrimeEnum

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open Filter Topology

/-- **Theorem 10.1** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.95.

"There is a deterministic algorithm with the following properties. It takes as input positive
integers N and Y such that 2 ⩽ Y ⩽ N^{1/2}. Its output is a bit array (u_1, …, u_{N−1}) such
that u_n = 1 if and only if n is Y-rough. Its running time is O(N log Y)."

**Formalization Note.** One machine, one output tape and one constant `K`, all before the input.
The input is the framed pair of binary words of `N, Y`; for integers, `Y ⩽ N^{1/2}` is `Y² ⩽ N`.
The output `roughArray N Y` is the list `u_1, …, u_{N−1}` (`true` = 1). `log` is natural; at
`Y ⩾ 2` it needs no clipping. -/
theorem theorem_10_1 :
    ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (K : ℝ), 0 < K ∧
      ∀ N Y : ℕ, 2 ≤ Y → Y ^ 2 ≤ N →
        RunsWithin A out (Encoding.encodeList id [binWord N, binWord Y]) (roughArray N Y)
          (K * N * Real.log (Y : ℝ)) := by sorry

end FasterPrimeEnum
