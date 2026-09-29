-- Prove2me | Theorems.Thm_Erdos52_rudnev_stevens_exponent
-- name    : Erdos52.rudnev_stevens_exponent
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T16:41:08.057997+00:00
-- url     : https://prove2.me/theorems/2322db94-fcf2-4194-9b4e-5275afd8e76c
-- title:
--   Rudnev–Stevens: exponent $4/3+2/1167$
-- statement:
--   For every $\varepsilon$ with $0<\varepsilon<1$ there is a constant $C_\varepsilon>0$ such that for every finite set $A\subset\mathbb Z$,
--
--   $$\max\bigl(|A+A|,\,|AA|\bigr)\ \ge\ C_\varepsilon\,|A|^{\frac43+\frac{2}{1167}-\varepsilon}.$$
--
--   This is a consequence of the Rudnev–Stevens bound (2022), which improved the exponents obtained after the Konyagin–Shkredov breakthrough past $4/3$.
--
--   **Formalization Note** The restriction $\varepsilon<1$ keeps the exponent positive, so that the empty set gives the trivial inequality $0\ge0$ (without it, $\varepsilon=\tfrac43+\tfrac2{1167}$ would give the junk value $0^0=1$ and make the statement false).
-- source:
--   https://www.erdosproblems.com/52; see the milestone description for the literature reference

import Mathlib
open scoped Pointwise

namespace Erdos52
theorem rudnev_stevens_exponent : ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
    (max (A + A).card (A * A).card : ℝ) ≥
      C * (A.card : ℝ) ^ ((4 : ℝ) / 3 + 2 / 1167 - ε) := by sorry
end Erdos52
