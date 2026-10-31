-- Prove2me | Theorems.Thm_EDPMBandit_lemma_7
-- name    : EDPMBandit.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:00:16.677713+00:00
-- url     : https://prove2.me/theorems/5e315279-99c1-47d3-ab86-08173a413a89
-- title:
--   Lemma 7 — the integral $\int_1^\infty x^{2m+1}e^{-ax^2}dx$
-- statement:
--   For every real $a>0$ and integer $m\ge0$,
--
--   $$
--   \int_1^\infty x^{2m+1}e^{-ax^2}\,dx=\frac{e^{-a}}{2a^{m+1}}\sum_{j=0}^m\frac{m!}{j!}a^j,
--   $$
--
--   and if moreover $a\ge3$, then
--
--   $$
--   \int_1^\infty x^{2m+1}e^{-ax^2}\,dx\le\frac{m!\,e^{-a}}2.
--   $$
--
--   This computation turns the tail bound of Lemma 2 into the moment bounds of Lemma 6.
--
--   **Formalization Note** The improper integral is the Lebesgue integral over $(1,\infty)$; both claims form one conjunction.
--
--   Differences from the source: none.
-- source:
--   Cassel–Mannor–Zeevi, A General Framework for Bandit Problems Beyond Cumulative Objectives, arXiv:1806.01380v3, pp.27–28, Lemma 7

import Mathlib

open MeasureTheory

namespace EDPMBandit

/-- Lemma 7, Cassel–Mannor–Zeevi, arXiv:1806.01380v3, pp.27–28: "For any real a > 0 and integer
m ≥ 0 we have that ∫_1^∞ x^{2m+1} exp(−ax²) dx = (exp(−a)/(2a^{m+1})) ∑_{j=0}^m (m!/j!) a^j. If
a ≥ 3 then we also have that ∫_1^∞ x^{2m+1} exp(−ax²) dx ≤ m! exp(−a)/2."

**Formalization Note.** The improper integral over `[1, ∞)` is the Lebesgue integral over
`Set.Ioi 1` (the integrand is integrable there). Both claims are one conjunction. -/
theorem lemma_7 (a : ℝ) (ha : 0 < a) (m : ℕ) :
    (∫ x in Set.Ioi (1 : ℝ), x ^ (2 * m + 1) * Real.exp (-(a * x ^ 2))) =
        Real.exp (-a) / (2 * a ^ (m + 1)) *
          ∑ j ∈ Finset.range (m + 1), ((m.factorial : ℝ) / (j.factorial : ℝ)) * a ^ j ∧
      (3 ≤ a →
        (∫ x in Set.Ioi (1 : ℝ), x ^ (2 * m + 1) * Real.exp (-(a * x ^ 2))) ≤
          (m.factorial : ℝ) * Real.exp (-a) / 2) := by sorry

end EDPMBandit
