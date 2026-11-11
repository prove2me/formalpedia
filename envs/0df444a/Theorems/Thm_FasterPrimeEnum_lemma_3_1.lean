-- Prove2me | Theorems.Thm_FasterPrimeEnum_lemma_3_1
-- name    : FasterPrimeEnum.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:38:57.638974+00:00
-- url     : https://prove2.me/theorems/339e497c-67ce-456d-997e-48f8d8de3b09
-- title:
--   Lemma 3.1 — bit array ⇄ sorted list in time $O(n+\mathrm{wt}(v)\log n)$ (corrected: $+1$ at $n=0$)
-- statement:
--   Let $v\in\mathbb F_2^n$ and let $\mathrm{wt}(v)$ be the number of $i\in\{0,\dots,n-1\}$ with $v_i=1$. A multitape Turing machine converts $v$ from the binary array format (the $n$ bits of $v$) to the sorted list format (the indices $i$ with $v_i=1$, in increasing order), and another converts it back, each in time
--
--   $$
--   O\big(n+\mathrm{wt}(v)\log n+1\big).
--   $$
--
--   The paper states $O(n+\mathrm{wt}(v)\log n)$; the term $1$ is needed only at $n=0$. The two formats are interchangeable at this cost, which the algorithm uses repeatedly to move between sieve arrays and lists of integers.
--
--   **Formalization Note** Two machines, one per direction, each with its constant before $v$. The list format is the framed list of the indices in binary; the list-to-array machine also receives $n$ in binary. The logarithm is clipped, $\log n=\log\max(n,2)$.
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) and RunsWithin (a halted run with exactly the output on a designated tape, within the time bound); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a constant factor is a shift of the exponent's o(1), or a change of the O-constant); an existential over the more restricted machine is the stronger statement
--   - correction: time O(n + wt(v) log n) → time K·(n + wt(v)·logU n + 1); reason: at v = [] (n = 0, every assumption holds) the printed bound is 0, but no run halts in 0 steps since the start state is not halted (proved as not_runsWithin_zero in the sanity file); adding 1 is the minimal fix and changes nothing for n ≥ 1
--   - encoding: binary array format and sorted list format → the array is the List Bool v; the list is Encoding.encodeList binWord of the increasing indices; the list-to-array input is Encoding.encodeList id [binWord n, that list]; reason: the paper fixes no tape layout; n cannot be recovered from the list alone
--   - encoding: log x in complexity bounds → logU x = log max(x, 2) (the published ThreeSumApsp.logU), and log log x as logU (logU x); reason: the paper's convention (p.2): log x should be read as log max(x, 2); it changes no bound for large inputs
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Lemma 3.1, p.18

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_FasterPrimeEnum_RunsWithin
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log

set_option autoImplicit false

namespace FasterPrimeEnum

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open ThreeSumApsp
open Filter Topology

/-- **Lemma 3.1 (corrected: `+ 1` at `n = 0`)** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.18.

"Let v ∈ F₂^n and let wt(v) denote the number of i ∈ {0, …, n − 1} such that v_i = 1. We may
convert v between the binary array format and the sorted list format, in either direction, in time
O(n + wt(v) log n)." The binary array format represents `v` "as an array of n bits", and the sorted
list format lists "those indices i such that v_i = 1 in increasing order" (p.18).

**Formalization Note.** Two machines, one per direction, each with its constant before `v`. Array
to list: the input is the bit list `v`; the output is the framed list of the indices `i` with
`v_i = 1`, increasing, in binary. List to array: the input is the framed pair of `n` (binary) and
that index list; the output is `v`. The bound is `K(n + wt(v) log n + 1)` with the clipped `log`
(p.2), `logU u = log max(u, 2)`. The `+ 1` corrects the printed bound at `n = 0`: there it is `0`, but no run halts in `0`
steps. -/
theorem lemma_3_1 :
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (K : ℝ), 0 < K ∧
      ∀ v : List Bool,
        RunsWithin A out v
          (Encoding.encodeList binWord ((List.range v.length).filter fun i => v.getD i false))
          (K * ((v.length : ℝ) + (v.count true : ℝ) * logU (v.length : ℝ) + 1))) ∧
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (K : ℝ), 0 < K ∧
      ∀ v : List Bool,
        RunsWithin A out
          (Encoding.encodeList id [binWord v.length,
            Encoding.encodeList binWord ((List.range v.length).filter fun i => v.getD i false)])
          v
          (K * ((v.length : ℝ) + (v.count true : ℝ) * logU (v.length : ℝ) + 1))) := by sorry

end FasterPrimeEnum
