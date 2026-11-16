-- Prove2me | Theorems.Thm_FasterPrimeEnum_Supplement_theorem_1_3
-- name    : FasterPrimeEnum.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:49:55.909061+00:00
-- url     : https://prove2.me/theorems/68f2b574-4f68-4477-97af-b935ff180f99
-- title:
--   Theorem 1.3 — a probabilistic machine lists the primes $p<N$ or fails with probability $\le 1/2$, in time $N(\log\log N)^{2+o(1)}$
-- statement:
--   There is a probabilistic multitape Turing machine — one that may flip an independent unbiased coin at each step — with the following properties. Its input is a positive integer $N$. Its output is either the list of all primes $p<N$ (in increasing order, in binary) or “FAIL”, and the second case occurs with probability at most $1/2$. It runs in time
--
--   $$
--   N(\log\log N)^{2+o(1)}.
--   $$
--
--   A returned list is always correct, so repeating the algorithm until it succeeds gives a provably correct list with expected running time of the same order. Compared with Sergeev's $O(N\log N)$ bound, this removes every positive power of $\log N$ from the cost.
--
--   **Formalization Note** One machine, one output tape, one coin tape and one $\varepsilon(N)\to0$ (the $o(1)$), all fixed before $N$. With $\tau(N)=N(\log\log N)^{2+\varepsilon(N)}$ (clipped logarithms) and $L=\lceil\tau(N)\rceil$, the coins are the $2^L$ strings of $L$ bits. For every coin string the run halts within $\tau(N)$ steps returning the list or FAIL, and FAIL occurs for at most half of the strings.
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) with RunsWithin / RunOutcome (a halted run within the time bound, with exactly the output on a designated tape); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a change of the O-constant or a shift of an o(1) exponent); an existential over the more restricted machine is the stronger statement
--   - encoding: a probabilistic Turing machine flipping an independent unbiased coin at each step; probability of FAIL → a PrimitiveMachine with a coin tape holding a string of L = ⌈τ(N)⌉ bits; the number of coin strings giving FAIL is at most 2^L/2; reason: a run of at most τ(N) steps reads at most the first L coin cells, so the uniform distribution on these strings is the distribution of the coin flips; reading a coin from the tape and flipping one per step simulate each other with a constant-factor loss in time
--   - encoding: output “FAIL” → the machine halts with answer bit false (RunOutcome … none); a returned word is answer bit true with the word on the output tape; reason: the paper fixes no encoding of FAIL; the answer bit makes FAIL distinct from every returned word
--   - reading: It runs in time N(log log N)^{2+o(1)} → the time bound holds on every coin string, with one ε → 0 chosen before N; reason: the paper's bound is a worst-case bound on each run: p.4 obtains the expected time of the repeated algorithm from (1.5), which needs (1.5) for every run
--   - encoding: log x and log log x in complexity bounds → logU x = log max(x, 2) and logU (logU x); reason: the paper's convention (p.2): in complexity bounds log x should be read as log max(x, 2)
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Theorem 1.3, p.4

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_FasterPrimeEnum_primesBelow
import Definitions.Def_FasterPrimeEnum_Supplement_RunOutcome

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open ThreeSumApsp
open Filter Topology

open Classical in
/-- **Theorem 1.3 (Probabilistic enumeration of primes)** — D. Harvey, *Faster enumeration of
primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.4.

"There is a probabilistic Turing machine with the following properties. Its input is a positive
integer N. Its output is either the list of all primes p < N, or "FAIL". The second case occurs
with probability at most 1/2. It runs in time (1.5) N(log log N)^{2+o(1)}." (p.4: "By a
probabilistic Turing machine, we mean a Turing machine that is allowed to flip an independent,
unbiased coin at each step.")

**Formalization Note.** One machine `A`, an output tape `out`, a coin tape `coin` and one `ε → 0`
(the `o(1)`), all chosen before `N`. Write `τ(N) = N · (log log N)^{2 + ε(N)}` with clipped
logarithms (p.2), and `L = ⌈τ(N)⌉`. The coins are a string of `L` bits on the coin tape; a run of at
most `τ(N)` steps reads at most its first `L` cells, so the uniform distribution on these strings is
the distribution of the coin flips. For **every** coin string the run halts within `τ(N)` steps
(worst-case time) with either the list of all primes `p < N` (increasing, in binary, answer bit
`true`) or "FAIL" (answer bit `false`), and FAIL occurs for at most half of the `2^L` strings. -/
theorem theorem_1_3 :
    ∃ (A : PrimitiveMachine) (out coin : Fin A.tapeCount) (ε : ℕ → ℝ),
      Tendsto ε atTop (𝓝 0) ∧
      ∀ N : ℕ, 1 ≤ N →
        (∀ coins : Fin ⌈(N : ℝ) * logU (logU (N : ℝ)) ^ (2 + ε N)⌉₊ → Bool,
          RunOutcome A (coinInit A coin (binWord N) (List.ofFn coins)) out
              ((N : ℝ) * logU (logU (N : ℝ)) ^ (2 + ε N))
              (some (Encoding.encodeList binWord (primesBelow N))) ∨
            RunOutcome A (coinInit A coin (binWord N) (List.ofFn coins)) out
              ((N : ℝ) * logU (logU (N : ℝ)) ^ (2 + ε N)) none) ∧
        2 * ((Finset.univ.filter fun coins : Fin ⌈(N : ℝ) * logU (logU (N : ℝ)) ^ (2 + ε N)⌉₊ → Bool =>
            RunOutcome A (coinInit A coin (binWord N) (List.ofFn coins)) out
              ((N : ℝ) * logU (logU (N : ℝ)) ^ (2 + ε N)) none).card) ≤
          2 ^ ⌈(N : ℝ) * logU (logU (N : ℝ)) ^ (2 + ε N)⌉₊ := by sorry

end Supplement

end FasterPrimeEnum
