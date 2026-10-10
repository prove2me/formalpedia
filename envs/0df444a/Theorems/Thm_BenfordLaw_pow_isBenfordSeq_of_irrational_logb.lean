-- Prove2me | Theorems.Thm_BenfordLaw_pow_isBenfordSeq_of_irrational_logb
-- name    : BenfordLaw.pow_isBenfordSeq_of_irrational_logb
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:35:21.901821+00:00
-- url     : https://prove2.me/theorems/f488996b-44bd-4d71-b4fa-07603053c706
-- title:
--   Powers $k^n$ satisfy Benford's law when $\log_{10}k$ is irrational
-- statement:
--   Let $k$ be a natural number such that $\log_{10}k$ is irrational (equivalently, $k\ge1$ is not a power of $10$). Then the sequence $k^1,k^2,k^3,\dots$ satisfies Benford's law in base $10$: for every $d\in\{1,\dots,9\}$,
--   $$\lim_{N\to\infty}\frac{\#\{1\le n\le N : D_{10}(k^n)=d\}}{N}=\log_{10}\!\left(1+\frac1d\right).$$
--
--   This is the goal theorem of the mission; the powers of $2$ are the case $k=2$.
--
--   **Formalization Note.** Encoded as `IsBenfordSeq 10 (fun n => (k : ℝ) ^ (n + 1))`. The case $k=0$ is excluded automatically because $\log_{10}0 = 0$ in Lean, which is rational.
-- source:
--   Wikipedia, "Benford's law" (https://en.wikipedia.org/wiki/Benford%27s_law), snapshot uploaded by the proposer, section "Distributions known to obey Benford's law", Note 3 ("the sequence k1, k2, k3, etc., satisfies Benford's law exactly, under the condition that log10 k is an irrational number").

import Mathlib
import Definitions.Def_BenfordLaw_Defs

namespace BenfordLaw

theorem pow_isBenfordSeq_of_irrational_logb (k : ℕ) (hk : Irrational (Real.logb 10 k)) :
    IsBenfordSeq 10 (fun n => (k : ℝ) ^ (n + 1)) := by sorry

end BenfordLaw
