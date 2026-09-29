-- Prove2me | Theorems.Thm_Devaney_period_three_implies_all_periods
-- name    : Devaney.period_three_implies_all_periods
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:11:07.991708+00:00
-- url     : https://prove2.me/theorems/50ed7397-0363-451a-b008-5243830e8af4
-- title:
--   Theorem 10.1 — period three implies all periods
-- statement:
--   Let $f : \mathbb{R} \to \mathbb{R}$ be continuous and suppose $f$ has a periodic point of prime period three. Then $f$ has a periodic point of prime period $n$ for every $n \ge 1$.
--
--   This is the celebrated special case of Sarkovskii's theorem — the "period three implies chaos" phenomenon of Li and Yorke — and Devaney proves it as a warm-up, using only the two covering observations.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.10, pp. 60–62, Theorem 10.1

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem period_three_implies_all_periods (f : ℝ → ℝ) (hf : Continuous f)
    (h3 : ∃ x, HasPrimePeriod f x 3) (n : ℕ) (hn : 0 < n) :
    ∃ x, HasPrimePeriod f x n := by sorry
end Devaney
