-- Prove2me | Theorems.Thm_Erdos52_solymosi_four_thirds
-- name    : Erdos52.solymosi_four_thirds
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T16:36:12.965279+00:00
-- url     : https://prove2.me/theorems/98bc26ef-fbdf-44fb-8263-000027efa721
-- title:
--   Solymosi: exponent $4/3$ up to logarithms
-- statement:
--   There is an absolute constant $C>0$ such that for every finite set $A\subset\mathbb Z$ with $|A|\ge 2$,
--
--   $$\max\bigl(|A+A|,\,|AA|\bigr)\ \ge\ C\,\frac{|A|^{4/3}}{(\log|A|)^{1/3}},$$
--
--   where $\log$ is the natural logarithm. This is the consequence of Solymosi's multiplicative-energy bound (2009), and was the record exponent for several years.
--
--   **Formalization Note** The hypothesis $|A|\ge2$ ensures $\log|A|>0$, avoiding division by zero.
-- source:
--   https://www.erdosproblems.com/52; see the milestone description for the literature reference

import Mathlib
open scoped Pointwise

namespace Erdos52
theorem solymosi_four_thirds : ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ), 2 ≤ A.card →
    (max (A + A).card (A * A).card : ℝ) ≥
      C * (A.card : ℝ) ^ ((4 : ℝ) / 3) / Real.log (A.card : ℝ) ^ ((1 : ℝ) / 3) := by sorry
end Erdos52
