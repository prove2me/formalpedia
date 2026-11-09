-- Prove2me | Theorems.Thm_CyclicForrelation_Even_nonadaptive_lower_bound
-- name    : CyclicForrelation.Even.nonadaptive_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:43.157564+00:00
-- url     : https://prove2.me/theorems/fbcd3274-b737-42bc-afaa-528ddac0bf65
-- title:
--   Theorem 4 — even-cycle nonadaptive lower bound
-- statement:
--   Let $n\in\mathbb N$, $N=2^n$, $m\ge2$, and $0<\varepsilon<1$. Every randomized nonadaptive estimator that succeeds on every sign-function tuple with probability at least $2/3$ has complexity satisfying
--   $$R^{\mathrm{na}}_\varepsilon(T_{2m})\ge\frac m{48}\min\{N,N^{1-1/m}\varepsilon^{-2/m}\}.$$
--   The bound permits arbitrary correlations between query locations and counts total queries over all oracles, with a bound at every seed. It includes both the accuracy-dependent regime and saturation at scale $mN$.
--
--   **Formalization Note** The printed Ω is instantiated uniformly by $1/48$. Eq. (14) gives $m3^{-1/m}N^{1-1/m}$; Eq. (18) gives $(m/24)N^{1-1/m}\varepsilon^{-2/m}$ for $\sqrt{3/N}\le\varepsilon\le1/8$. If $N\ge192$, monotonicity at $\sqrt{3/N}$ gives $mN/(24\,3^{1/m})\ge mN/48$ below that threshold. For $\varepsilon\ge1/8$, Eq. (14) is at least the target with this certificate. For $N<192$, $(3N)^{1/m}<24$ makes Eq. (14) at least $mN/24$.
--
--   Differences from the source:
--   - generalization: a uniform Ω bound with an unspecified absolute constant → the numerical lower certificate 1/48, independent of n, m, and ε; reason: Eqs. (14) and (18), pp. 12–13, give this certificate throughout the full stated domain
--   - encoding: minimum total worst-case nonadaptive oracle queries at success 2/3 → least achievable natural cost in the measurable private-seed query-list model; reason: queries are fixed before answers, postprocessing sees only answers and the seed, and exhaustive evaluation proves feasibility before minimization
--   - encoding: one-based sign-function tuples on the binary cube → zero-based finite indices and Boolean signs interpreted as real ±1; reason: these are bijective encodings, with the closing cycle edge and every input tuple preserved
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), p. 11, Theorem 4, Eq. (11); pp. 12–13, Eqs. (14), (18) and final paragraph

import Definitions.Def_CyclicForrelation_Even_complexity
import Definitions.Def_CyclicForrelation_Even_multiShift

namespace CyclicForrelation.Even

/-- Theorem 4 with the uniform certificate 1/48 from Eqs. (14), (18) and monotonicity. -/
theorem nonadaptive_lower_bound (n m : ℕ) (hm : 2 ≤ m) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    (m : ℝ) / 48 * evenScale n m ε ≤ (nonadaptiveComplexity n (2 * m) ε : ℝ) := by sorry

end CyclicForrelation.Even
