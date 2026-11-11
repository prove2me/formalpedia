-- Prove2me | Theorems.Thm_FasterPrimeEnum_theorem_1_2
-- name    : FasterPrimeEnum.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:39:16.040693+00:00
-- url     : https://prove2.me/theorems/782cbb4a-cec6-4186-8d60-a8217d0472fa
-- title:
--   Theorem 1.2 — a deterministic Turing machine lists the primes $p<N$ in time $N(\log N)^{1/2}(\log\log N)^{1+o(1)}$
-- statement:
--   There is a Turing machine with the following properties. Its input is a positive integer $N$, and its output is the list of all primes $p<N$, written in standard binary and in increasing order. It runs in time
--
--   $$
--   N(\log N)^{1/2}(\log\log N)^{1+o(1)}.
--   $$
--
--   This improves the previous best bit complexity $O(N\log N)$ (Sergeev) by a factor of almost $(\log N)^{1/2}$, the first speedup by a positive power of $\log N$ over the sieve of Eratosthenes; the output alone has $\Theta(N)$ bits.
--
--   **Formalization Note** One machine, one output tape and one function $\varepsilon(N)\to0$ for the $o(1)$, all chosen before $N$, and the bound holds at every $N\ge1$. The output is the list of all primes below $N$, increasing, each in standard binary, framed by the published list encoding. Logarithms are clipped, $\log x=\log\max(x,2)$, so the bound is positive at every $N$.
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) and RunsWithin (a halted run with exactly the output on a designated tape, within the time bound); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a constant factor is a shift of the exponent's o(1), or a change of the O-constant); an existential over the more restricted machine is the stronger statement
--   - encoding: input a positive integer N; output the list of all primes p < N in standard binary notation, in increasing order (p.4) → input binWord N; output Encoding.encodeList binWord (primesBelow N) on a designated tape of the halted machine; reason: framing the list is a constant factor in length and fixes where one prime ends
--   - encoding: time N(log N)^{1/2}(log log N)^{1+o(1)} → N·logU(N)^{1/2}·logU(logU N)^{1 + ε(N)} with one ε → 0 chosen before N, for every N ≥ 1; reason: this is what the O / o(1) notation means for one algorithm (§1.1, p.1); the constants are chosen before every input
--   - encoding: log x in complexity bounds → logU x = log max(x, 2) (the published ThreeSumApsp.logU), and log log x as logU (logU x); reason: the paper's convention (p.2): log x should be read as log max(x, 2); it changes no bound for large inputs
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Theorem 1.2, p.4; §1.4, p.4 (output format)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_FasterPrimeEnum_primesBelow

set_option autoImplicit false

namespace FasterPrimeEnum

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open ThreeSumApsp
open Filter Topology

/-- **Theorem 1.2 (Deterministic enumeration of primes)** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.4.

"There is a Turing machine with the following properties. Its input is a positive integer N and
its output is the list of all primes p < N. It runs in time N(log N)^{1/2}(log log N)^{1+o(1)}."

**Formalization Note.** One machine `A` and one output tape `out`, chosen before `N`, and one
function `ε → 0` (the `o(1)`), also chosen before `N`. The input is `N` in standard binary
(`binWord`, most significant bit first). The output is the list of all primes `p < N` in increasing
order, each in standard binary (p.4), framed by the published `Encoding.encodeList`. The bound holds
at every `N ≥ 1`. Logarithms are clipped, `log x = log max(x, 2)` (p.2): `log N` is `logU N` and `log log N` is
`logU (logU N)` (the published `ThreeSumApsp.logU u = log max(u, 2)`), both at least `log 2`, and
the exponents `1/2` and `1 + ε N` are real powers of positive numbers. -/
theorem theorem_1_2 :
    ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (ε : ℕ → ℝ),
      Tendsto ε atTop (𝓝 0) ∧
      ∀ N : ℕ, 1 ≤ N →
        RunsWithin A out (binWord N) (Encoding.encodeList binWord (primesBelow N))
          ((N : ℝ) * logU (N : ℝ) ^ (1 / 2 : ℝ) * logU (logU (N : ℝ)) ^ (1 + ε N)) := by sorry

end FasterPrimeEnum
