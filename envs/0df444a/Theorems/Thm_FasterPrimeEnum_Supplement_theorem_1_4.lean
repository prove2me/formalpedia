-- Prove2me | Theorems.Thm_FasterPrimeEnum_Supplement_theorem_1_4
-- name    : FasterPrimeEnum.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:50:33.794929+00:00
-- url     : https://prove2.me/theorems/de200cc2-858a-40e3-89db-c3de9cbeb97f
-- title:
--   Theorem 1.4 — a deterministic machine lists the primes $p<N$ or fails, never failing under Conjecture 7.1, in time $N(\log\log N)^{1+o(1)}$
-- statement:
--   There is a deterministic multitape Turing machine with the following properties. Its input is a positive integer $N$. Its output is either the list of all primes $p<N$ (in increasing order, in binary) or “FAIL”. If Conjecture 7.1 is true — for all real $x\ge2$, the interval $(x,x+\log^3x]$ contains fewer than $3\log^2x$ square-primes — then the second case never occurs. It runs in time
--
--   $$
--   N(\log\log N)^{1+o(1)}.
--   $$
--
--   The algorithm never outputs a wrong list, even if the conjecture is false; a FAIL would disprove the conjecture. Under the conjecture the cost per prime is $\log N(\log\log N)^{1+o(1)}$, barely more than one multiplication of $\log N$-bit integers.
--
--   **Formalization Note** One machine, one output tape and one $\varepsilon(N)\to0$, fixed before $N$. The machine and its time bound are unconditional; only “the outcome is the list” depends on Conjecture 7.1, which appears as an implication inside the statement.
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) with RunsWithin / RunOutcome (a halted run within the time bound, with exactly the output on a designated tape); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a change of the O-constant or a shift of an o(1) exponent); an existential over the more restricted machine is the stronger statement
--   - encoding: output “FAIL” → the machine halts with answer bit false (RunOutcome … none); a returned word is answer bit true with the word on the output tape; reason: the paper fixes no encoding of FAIL; the answer bit makes FAIL distinct from every returned word
--   - encoding: log x and log log x in complexity bounds → logU x = log max(x, 2) and logU (logU x); reason: the paper's convention (p.2): in complexity bounds log x should be read as log max(x, 2)
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Theorem 1.4, p.5; Conjecture 7.1 and eq. (7.1), p.57

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_FasterPrimeEnum_primesBelow
import Definitions.Def_FasterPrimeEnum_Supplement_RunOutcome
import Definitions.Def_FasterPrimeEnum_Supplement_Conjecture71

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open ThreeSumApsp
open Filter Topology

/-- **Theorem 1.4 (Heuristic enumeration of primes)** — D. Harvey, *Faster enumeration of primes*,
arXiv:2606.22851 (held version, sha256 7fc13f17…), p.5.

"There is a (deterministic) Turing machine with the following properties. Its input is a positive
integer N. Its output is either the list of all primes p < N, or "FAIL". If Conjecture 7.1 is true,
then the second case never occurs. It runs in time (1.6) N(log log N)^{1+o(1)}."

**Formalization Note.** One machine, one output tape and one `ε → 0`, all chosen before `N`. The
machine and its time bound are unconditional: on every `N ≥ 1` it halts within
`N (log log N)^{1+ε(N)}` steps (clipped logarithms, p.2) with outcome either the list of all primes
`p < N` (increasing, in binary) or "FAIL" (answer bit `false`). Only "the outcome is not FAIL" is
conditional, on Conjecture 7.1 (p.57) as an implication inside the statement. -/
theorem theorem_1_4 :
    ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (ε : ℕ → ℝ),
      Tendsto ε atTop (𝓝 0) ∧
      ∀ N : ℕ, 1 ≤ N →
        ∃ o : Option (List Bool),
          RunOutcome A (A.init (binWord N)) out
              ((N : ℝ) * logU (logU (N : ℝ)) ^ (1 + ε N)) o ∧
            (o = none ∨ o = some (Encoding.encodeList binWord (primesBelow N))) ∧
            (Conjecture71 → o = some (Encoding.encodeList binWord (primesBelow N))) := by sorry

end Supplement

end FasterPrimeEnum
