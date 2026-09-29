-- Prove2me | Theorems.Thm_EulerMascheroni_denominator_gt_of_rational
-- name    : EulerMascheroni.denominator_gt_of_rational
-- status  : Open
-- author  : @shivm
-- created : 2026-09-10T06:58:50.379227+00:00
-- url     : https://prove2.me/theorems/8cf87993-b413-46d4-9a2f-8502f303264c
-- title:
--   A rational $\gamma$ would have denominator exceeding $10^{244663}$
-- statement:
--   If Euler's constant is rational, say $\gamma = p/q$ with $q \ge 1$, then
--
--   $$q \;>\; 10^{244663}.$$
--
--   This is a **theorem**, obtained by computation rather than by structural argument. Brent and McMillan established the bound $q > 10^{15000}$ in 1980, having computed $\gamma$ to $30{,}000$ decimal places by an algorithm based on the modified Bessel functions $I_0(2x)$ and $K_0(2x)$; Papanikolaou extended the continued-fraction analysis in 1997 to reach the bound stated here.
--
--   The reasoning is that a rational with small denominator would appear as a convergent of the continued fraction expansion of $\gamma$, so verifying that no convergent with denominator below the bound equals $\gamma$ to the computed precision excludes every such rational. It measures the reach of computation rather than progress toward a proof: no finite computation can establish irrationality.
--
--   **Formalization note.** This is a genuinely hard formalization target, since it encodes a large high-precision computation; it is included so the mission's dependency graph is truthful about what is known, not because a direct proof is within reach of current tooling.
-- source:
--   R. P. Brent and E. M. McMillan, Some new algorithms for high-precision computation of Euler's constant, Math. Comp. 34 (1980), 305-312 (bound 10^15000); T. Papanikolaou (1997) extended the continued-fraction computation to the bound 10^244663, as reported in J. Lagarias, Bull. AMS 50 (2013), https://arxiv.org/abs/1303.1856, Section 5.

import Definitions.Def_eulerMascheroni_gompertz

open Real

namespace EulerMascheroni
theorem denominator_gt_of_rational (p : ℤ) (q : ℕ) (hq : 0 < q)
    (h : Real.eulerMascheroniConstant = (p : ℝ) / (q : ℝ)) :
    (10 : ℕ) ^ 244663 < q := by sorry
end EulerMascheroni
