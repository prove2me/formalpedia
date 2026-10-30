-- Prove2me | Theorems.Thm_FMMM_TSM_min_ratio_eq_alpha
-- name    : FMMM.TSM.min_ratio_eq_alpha
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:29:06.229989+00:00
-- url     : https://prove2.me/theorems/8db15231-2697-40a2-bee5-214e6eeb3632
-- title:
--   §4.2.4, p. 9: the minimum of the three ratios is $\alpha$
-- statement:
--   The three denominators below are positive, and
--
--   $$\min\left\{\frac{1 - \frac{1}{e^2}}{\frac53 - \frac{4}{3e}},\ \frac{1 - \frac{2}{e^2}}{\frac43 - \frac{2}{3e}},\ \frac{1 - \frac{3}{2e}}{1 - \frac1e}\right\} = \min\{.735\ldots,\ .670\ldots,\ .709\ldots\} = \frac{1 - \frac{2}{e^2}}{\frac43 - \frac{2}{3e}} = \alpha \approx .670.$$
--
--   These are the ratios of the coefficients of $|A_{BB}|$, $|A_{BR}|$ and $|A_B| + |A_R|$ in the lower bound on $\mathrm{ALG}$ and the upper bound on $\mathrm{OPT}$; their minimum is the approximation ratio of the algorithm.
--
--   Differences from the source:
--   - reading: the decimal values .735…, .670…, .709… → the three ratios lie in [0.735, 0.736), [0.670, 0.671), [0.709, 0.710); reason: "…" denotes truncated decimal expansions
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.4, p. 9 (unnumbered display)

import Mathlib
import Definitions.Def_FMMM_TSM_alpha

namespace FMMM.TSM

/-- **The minimum of the three coefficient ratios is `α`.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.4, p. 9 (unnumbered display): "min{(1 − 1/e²)/(5/3 − 4/(3e)), (1 − 2/e²)/(4/3 − 2/(3e)),
(1 − 3/(2e))/(1 − 1/e)} = min{.735 …, .670 …, .709 …} = (1 − 2/e²)/(4/3 − 2/(3e)) ≈ .670."

The three denominators are positive; the three ratios lie in `[0.735, 0.736)`, `[0.670, 0.671)`,
`[0.709, 0.710)`; and their minimum is `alpha`. -/
theorem min_ratio_eq_alpha :
    0 < 5 / 3 - 4 / (3 * Real.exp 1) ∧ 0 < 4 / 3 - 2 / (3 * Real.exp 1) ∧ 0 < 1 - 1 / Real.exp 1 ∧
    (0.735 ≤ (1 - 1 / Real.exp 2) / (5 / 3 - 4 / (3 * Real.exp 1)) ∧
      (1 - 1 / Real.exp 2) / (5 / 3 - 4 / (3 * Real.exp 1)) < 0.736) ∧
    (0.670 ≤ (1 - 2 / Real.exp 2) / (4 / 3 - 2 / (3 * Real.exp 1)) ∧
      (1 - 2 / Real.exp 2) / (4 / 3 - 2 / (3 * Real.exp 1)) < 0.671) ∧
    (0.709 ≤ (1 - 3 / (2 * Real.exp 1)) / (1 - 1 / Real.exp 1) ∧
      (1 - 3 / (2 * Real.exp 1)) / (1 - 1 / Real.exp 1) < 0.710) ∧
    min (min ((1 - 1 / Real.exp 2) / (5 / 3 - 4 / (3 * Real.exp 1)))
        ((1 - 2 / Real.exp 2) / (4 / 3 - 2 / (3 * Real.exp 1))))
      ((1 - 3 / (2 * Real.exp 1)) / (1 - 1 / Real.exp 1)) = alpha := by sorry

end FMMM.TSM
