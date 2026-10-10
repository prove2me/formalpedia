-- Prove2me | Theorems.Thm_BenfordLaw_pow_two_isBenfordSeq
-- name    : BenfordLaw.pow_two_isBenfordSeq
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:13.821981+00:00
-- url     : https://prove2.me/theorems/3e088a8e-23ae-435f-837b-c6d3e2f11b1f
-- title:
--   The powers of $2$ satisfy Benford's law
-- statement:
--   The sequence of powers of two, $2^1, 2^2, 2^3, \dots$, satisfies Benford's law in base $10$: for every $d \in \{1,\dots,9\}$,
--   $$\lim_{N\to\infty}\frac{\#\{1 \le n \le N : D_{10}(2^n) = d\}}{N} = \log_{10}\!\left(1+\frac1d\right).$$
--
--   This is the special case $k=2$ of the mission goal, listed separately in the source.
--
--   **Formalization Note.** Encoded as `IsBenfordSeq 10 (fun n => (2 : ℝ) ^ (n + 1))`, with $n$ starting at $0$.
-- source:
--   Wikipedia, "Benford's law" (https://en.wikipedia.org/wiki/Benford%27s_law), snapshot uploaded by the proposer, sections "Examples" and "Distributions known to obey Benford's law" ("the powers of 2", ref. Raimi 1976, https://doi.org/10.2307/2319349).

import Mathlib
import Definitions.Def_BenfordLaw_Defs

namespace BenfordLaw

theorem pow_two_isBenfordSeq :
    IsBenfordSeq 10 (fun n => (2 : ℝ) ^ (n + 1)) := by sorry

end BenfordLaw
