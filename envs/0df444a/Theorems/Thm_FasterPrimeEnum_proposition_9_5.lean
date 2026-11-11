-- Prove2me | Theorems.Thm_FasterPrimeEnum_proposition_9_5
-- name    : FasterPrimeEnum.proposition_9_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:39:07.846738+00:00
-- url     : https://prove2.me/theorems/0cd9047d-7f31-473e-adba-7dd32176ffbf
-- title:
--   Proposition 9.5 — testing square-primality in bulk
-- statement:
--   There is a deterministic algorithm, a multitape Turing machine, with the following properties. It takes as input an integer $N\ge1$ and a list $\mathcal R$ of distinct integers in $[1,N)$. It returns the sorted list of all square-primes in $\mathcal R$. Its running time is
--
--   $$
--   O(N)+|\mathcal R|(\log N)^{11.5+o(1)}.
--   $$
--
--   The deterministic algorithm uses it on the integers of the rejected intervals, whose number is small by Proposition 10.9.
--
--   **Formalization Note** One machine, one output tape, one $\varepsilon(N)\to0$ and one constant before the input. The input is the framed pair of $N$ (binary) and the list (each element in binary, in the given, not necessarily sorted order). The output is the increasing list of the square-primes in it, of either parity. The logarithm is clipped.
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) and RunsWithin (a halted run with exactly the output on a designated tape, within the time bound); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a constant factor is a shift of the exponent's o(1), or a change of the O-constant); an existential over the more restricted machine is the stronger statement
--   - encoding: input N and a list R of distinct integers; output a sorted list → input Encoding.encodeList id [binWord N, Encoding.encodeList binWord R] with R.Nodup; output Encoding.encodeList binWord S, S strictly increasing; reason: standard binary, framed; the paper fixes no tape layout
--   - encoding: O(N) + |R|(log N)^{11.5+o(1)} → K·N + |R|·logU(N)^{11.5 + ε(N)} with K and ε → 0 chosen before the input; reason: this is what the O / o(1) notation means for one algorithm (§1.1, p.1); the constants are chosen before every input
--   - encoding: log x in complexity bounds → logU x = log max(x, 2) (the published ThreeSumApsp.logU), and log log x as logU (logU x); reason: the paper's convention (p.2): log x should be read as log max(x, 2); it changes no bound for large inputs
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Proposition 9.5, p.89

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_FasterPrimeEnum_IsSquarePrime

set_option autoImplicit false

namespace FasterPrimeEnum

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open ThreeSumApsp
open Filter Topology

/-- **Proposition 9.5 (Testing square-primality in bulk)** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.89.

"There is a (deterministic) algorithm with the following properties. It takes as input an integer
N ⩾ 1 and a list R of (distinct) integers in [1, N). It returns a sorted list consisting of all
square-primes in R. Its running time is O(N) + |R|(log N)^{11.5+o(1)}."

**Formalization Note.** One machine, one output tape, one `ε → 0` and one constant `K`, all before
the input. The input is the framed pair of `N` (binary) and the list `R` (each element in binary,
in the given order, not necessarily sorted). The output is the increasing list of the square-primes
of `R` (of either parity), framed; it is determined by the two conditions. The logarithm is clipped
(p.2): `logU u = log max(u, 2)`. -/
theorem proposition_9_5 :
    ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (ε : ℕ → ℝ),
      Tendsto ε atTop (𝓝 0) ∧ ∃ K : ℝ, 0 < K ∧
      ∀ N : ℕ, 1 ≤ N → ∀ R : List ℕ, R.Nodup → (∀ n ∈ R, 1 ≤ n ∧ n < N) →
        ∃ S : List ℕ, S.Pairwise (· < ·) ∧ (∀ n, n ∈ S ↔ n ∈ R ∧ IsSquarePrime n) ∧
          RunsWithin A out (Encoding.encodeList id [binWord N, Encoding.encodeList binWord R])
            (Encoding.encodeList binWord S)
            (K * N + (R.length : ℝ) * logU (N : ℝ) ^ ((23 / 2 : ℝ) + ε N)) := by sorry

end FasterPrimeEnum
