-- Prove2me | Theorems.Thm_Erdos52_elekes_five_fourths
-- name    : Erdos52.elekes_five_fourths
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T16:34:13.37399+00:00
-- url     : https://prove2.me/theorems/320028fe-a44a-4283-beee-f0990691263e
-- title:
--   Elekes: exponent $5/4$
-- statement:
--   There is an absolute constant $C>0$ such that for every finite set $A\subset\mathbb Z$,
--
--   $$\max\bigl(|A+A|,\,|AA|\bigr)\ \ge\ C\,|A|^{5/4}.$$
--
--   This follows from Elekes' inequality $|A+A|\,|AA|\gg|A|^{5/2}$ (1997), the first application of incidence geometry to the sum–product problem.
-- source:
--   https://www.erdosproblems.com/52; see the milestone description for the literature reference

import Mathlib
open scoped Pointwise

namespace Erdos52
theorem elekes_five_fourths : ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
    (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ ((5 : ℝ) / 4) := by sorry
end Erdos52
