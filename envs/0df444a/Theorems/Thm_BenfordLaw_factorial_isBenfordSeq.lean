-- Prove2me | Theorems.Thm_BenfordLaw_factorial_isBenfordSeq
-- name    : BenfordLaw.factorial_isBenfordSeq
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:12.287704+00:00
-- url     : https://prove2.me/theorems/e08f823b-2bee-4693-8346-06230d41194c
-- title:
--   The factorials satisfy Benford's law
-- statement:
--   The sequence of factorials $1!, 2!, 3!, \dots$ satisfies Benford's law in base $10$: for every $d\in\{1,\dots,9\}$,
--   $$\lim_{N\to\infty}\frac{\#\{1\le n\le N : D_{10}(n!)=d\}}{N}=\log_{10}\!\left(1+\frac1d\right).$$
--
--   **Formalization Note.** Encoded as `IsBenfordSeq 10 (fun n => ((n + 1).factorial : ℝ))`.
-- source:
--   Wikipedia, "Benford's law" (https://en.wikipedia.org/wiki/Benford%27s_law), snapshot uploaded by the proposer, section "Distributions known to obey Benford's law" ("the factorials", ref. [56]).

import Mathlib
import Definitions.Def_BenfordLaw_Defs

namespace BenfordLaw

theorem factorial_isBenfordSeq :
    IsBenfordSeq 10 (fun n => ((n + 1).factorial : ℝ)) := by sorry

end BenfordLaw
