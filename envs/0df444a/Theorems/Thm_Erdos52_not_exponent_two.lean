-- Prove2me | Theorems.Thm_Erdos52_not_exponent_two
-- name    : Erdos52.not_exponent_two
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T16:41:32.761975+00:00
-- url     : https://prove2.me/theorems/1bfaf241-2e72-43fb-8bb9-8a9d4cfacf35
-- title:
--   The exponent $2$ is not attained
-- statement:
--   There is no constant $C>0$ such that
--
--   $$\max\bigl(|A+A|,\,|AA|\bigr)\ \ge\ C\,|A|^{2}$$
--
--   holds for every finite set $A\subset\mathbb Z$. The witnesses are the intervals $A=\{1,\dots,n\}$: the number of distinct products $ab$ with $1\le a,b\le n$ is $o(n^2)$ (Erdős' multiplication table problem). This shows that the loss of $|A|^{\varepsilon}$ in the conjecture is necessary.
-- source:
--   https://www.erdosproblems.com/52; see the milestone description for the literature reference

import Mathlib
open scoped Pointwise

namespace Erdos52
theorem not_exponent_two : ¬ ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
    (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 : ℝ) := by sorry
end Erdos52
