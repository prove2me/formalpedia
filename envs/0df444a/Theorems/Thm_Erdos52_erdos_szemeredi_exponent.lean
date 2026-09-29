-- Prove2me | Theorems.Thm_Erdos52_erdos_szemeredi_exponent
-- name    : Erdos52.erdos_szemeredi_exponent
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T16:31:25.226846+00:00
-- url     : https://prove2.me/theorems/9496eea4-b202-40f0-9c81-c8da6a6ff35b
-- title:
--   Erdős–Szemerédi: exponent $1+\delta$
-- statement:
--   There exist absolute constants $\delta>0$ and $C>0$ such that for every finite set $A\subset\mathbb Z$,
--
--   $$\max\bigl(|A+A|,\,|AA|\bigr)\ \ge\ C\,|A|^{1+\delta}.$$
--
--   This is the original theorem of Erdős and Szemerédi (1983), the first result showing that sumset and product set cannot both be of linear size.
-- source:
--   https://www.erdosproblems.com/52; see the milestone description for the literature reference

import Mathlib
open scoped Pointwise

namespace Erdos52
theorem erdos_szemeredi_exponent : ∃ (δ : ℝ), 0 < δ ∧ ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
    (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (1 + δ) := by sorry
end Erdos52
