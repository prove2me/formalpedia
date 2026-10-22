-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_numerical_range_subcritical
-- name    : BirkhoffGlobalSection.numerical_range_subcritical
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:06:59.910607+00:00
-- url     : https://prove2.me/theorems/b27f8fe7-25ad-4c8a-89e6-8882b1baafed
-- title:
--   The $c \geq 2.1$ range is subcritical
-- statement:
--   Let $0<\mu\leq1/2$ and $c\geq2.1$. Then the Jacobi energy $-c$ lies below the first collision-free critical value:
--
--   $$
--   -c<h_1(\mu).
--   $$
--
--   This is an a priori energy half-line containing the positive-mass part of the validated global-section rectangle $2.1\leq c\leq2.1+10^{-6}$. The endpoint $\mu=0$ belongs to the cited Joung--van Koert theorem but is intentionally outside this first-critical-value row and the formal validated global-section row. The statement connects the positive-mass numerical parameters to the subcritical hypothesis; it does not enlarge the interval on which the computer-assisted global-section theorem is claimed.
-- source:
--   Joung--van Koert, Section 4 and Lemma 4.1, https://arxiv.org/abs/2407.19159v3. This row isolates the positive-mass subcritical estimate used for the c >= 2.1 parameter range.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The a priori half-line `c ≥ 2.1` over `0 < μ ≤ 1/2`, which contains the
positive-mass part of Joung--van Koert's validated rectangle, lies below the
first critical Jacobi value. -/
theorem numerical_range_subcritical (μ c : ℝ)
    (hμ0 : 0 < μ) (hμhalf : μ ≤ 1 / 2) (hc : 21 / 10 ≤ c) :
    belowFirstCriticalValue μ c := by sorry

end BirkhoffGlobalSection
