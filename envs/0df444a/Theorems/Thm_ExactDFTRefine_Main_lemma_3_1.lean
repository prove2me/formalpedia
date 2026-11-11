-- Prove2me | Theorems.Thm_ExactDFTRefine_Main_lemma_3_1
-- name    : ExactDFTRefine.Main.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:01:39.526067+00:00
-- url     : https://prove2.me/theorems/99e4ff08-9fdc-4540-befe-1cd07734df50
-- title:
--   Lemma 3.1 — S_6(x) ≤ e^x for x ≥ 0, and e^x ≤ S_6(x) + (7/4320)x^6 for 0 ≤ x ≤ 1
-- statement:
--   Let $S_6(x) = \sum_{j=0}^{5} x^j/j!$ be the degree-five Taylor polynomial of the exponential. Then
--   $$S_6(x) \le e^x \quad (x \ge 0), \qquad e^x \le S_6(x) + \frac{7}{4320}x^6 \quad (0 \le x \le 1). \tag{4}$$
--   The two clauses have different domains: the lower bound holds on the whole half-line, the upper bound only on $[0, 1]$. These elementary enclosures are what Proposition 3.2 substitutes into each normalized moment term $m(r/145)^{1-C} = \frac{mr}{145}\exp(C\log\frac{145}{r})$.
--
--   Differences from the source: none.
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 3, Lemma 3.1 (Eq. (4))

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

/-- **Lemma 3.1**, p. 3. With `S_6(x) = ∑_{j=0}^{5} x^j/j!`: `S_6(x) ≤ e^x` for `x ≥ 0`, and
`e^x ≤ S_6(x) + (7/4320) x^6` for `0 ≤ x ≤ 1` (Eq. (4)). -/
theorem lemma_3_1 :
    (∀ x : ℝ, 0 ≤ x → SN 6 x ≤ Real.exp x) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ 1 → Real.exp x ≤ SN 6 x + 7 / 4320 * x ^ 6) := by sorry

end ExactDFTRefine.Main
