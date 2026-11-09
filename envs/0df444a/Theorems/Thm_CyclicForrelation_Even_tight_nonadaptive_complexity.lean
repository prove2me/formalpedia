-- Prove2me | Theorems.Thm_CyclicForrelation_Even_tight_nonadaptive_complexity
-- name    : CyclicForrelation.Even.tight_nonadaptive_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:50.172041+00:00
-- url     : https://prove2.me/theorems/a6ad2d48-ae56-474f-a7c8-cce75e4bfab0
-- title:
--   Section 1.1 Eq. (3) — tight nonadaptive complexity for even cycles
-- statement:
--   For every natural cube dimension $n$, every integer $m\ge2$, and every real $0<\varepsilon<1$, put $N=2^n$. The minimum total worst-case query cost of a randomized nonadaptive algorithm estimating the normalized cyclic trace on every arbitrary sign-function tuple with probability at least $2/3$ satisfies
--   $$\frac m{48}\min\{N,N^{1-1/m}\varepsilon^{-2/m}\}\le R^{\mathrm{na}}_\varepsilon(T_{2m})\le34m\min\{N,N^{1-1/m}\varepsilon^{-2/m}\}.$$
--   These are simultaneous bounds with absolute constants. Both the accuracy-dependent query scale and the exhaustive saturation scale are retained for all even cycle lengths at least four. The target is the cyclic normalized trace, including its closing edge, rather than a matrix entry along a path.
--
--   **Formalization Note** The lower constant is the $1/48$ certificate detailed in the Theorem 4 item, using Eqs. (14), (18) on pp. 12–13 and monotonicity in accuracy. On p. 18, $q_0=\lceil16N^{1-2/k}\varepsilon^{-4/k}\rceil$ gives success at least $3/4$ and cost at most $17k\min\{N,N^{1-2/k}\varepsilon^{-4/k}\}$. With $k=2m$, this yields $34m$ at success $2/3$ without confidence amplification. No parameter is absorbed into either constant.
--
--   Differences from the source:
--   - generalization: a uniform Θ bound with unspecified absolute constants → simultaneous numerical certificates 1/48 and 34, independent of n, m, and ε; reason: the lower certificate follows from Eqs. (14), (18) and monotonicity, while the p. 18 single-run certificate 17k at k=2m gives 34m
--   - encoding: minimum total worst-case nonadaptive oracle queries at success 2/3 → least achievable natural cost in the measurable private-seed query-list model; reason: queries are fixed before answers, postprocessing sees only answers and the seed, and exhaustive evaluation proves feasibility before minimization
--   - encoding: one-based sign-function tuples on the binary cube → zero-based finite indices and Boolean signs interpreted as real ±1; reason: these are bijective encodings, with the closing cycle edge and every input tuple preserved
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), p. 4, §1.1 Eq. (3), assembled from Theorems 4 and 10

import Definitions.Def_CyclicForrelation_Even_complexity

namespace CyclicForrelation.Even

/-- Section 1.1 Eq. (3), with absolute numerical certificates independent of every parameter. -/
theorem tight_nonadaptive_complexity (n m : ℕ) (hm : 2 ≤ m) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    (m : ℝ) / 48 * evenScale n m ε ≤ (nonadaptiveComplexity n (2 * m) ε : ℝ) ∧
    (nonadaptiveComplexity n (2 * m) ε : ℝ) ≤ 34 * (m : ℝ) * evenScale n m ε := by sorry

end CyclicForrelation.Even
