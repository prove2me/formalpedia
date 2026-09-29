-- Prove2me | Theorems.Thm_Erdos142_behrend_lower_bound
-- name    : Erdos142.behrend_lower_bound
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:39:38.885789+00:00
-- url     : https://prove2.me/theorems/dbe7e7d4-64c7-4b5a-b68f-425c5ba8d155
-- title:
--   Behrend's lower bound: $r_3(N) \ge N e^{-4\sqrt{\log N}}$
-- statement:
--   For every $N$,
--
--   $$N\,e^{-4\sqrt{\log N}} \;\le\; r_3(N).$$
--
--   Behrend's 1946 construction produces a subset of $\{1,\dots,N\}$ of this size containing no non-trivial three-term arithmetic progression, by taking integers whose digits in a suitable base are the coordinates of lattice points on a sphere; strict convexity of the sphere prevents any point from being the midpoint of two others, which is exactly the three-term condition. The explicit constant $4$ in the exponent is the one carried by the formalized version in Mathlib.
--
--   This bound is the reason the problem is hard rather than merely unsolved. It shows the truth at $k = 3$ is of the shape $N\exp(-\Theta(\sqrt{\log N}))$, so no asymptotic formula can be a power of $\log N$, and it places an absolute ceiling on how strong an upper bound can be: no argument may prove $r_3(N) \le N\exp(-(\log N)^{1/2+\varepsilon})$. Together with the monotonicity milestone it yields the same lower bound for every $k \ge 3$.
-- source:
--   F. A. Behrend, On sets of integers which contain no three terms in arithmetical progression, Proc. Nat. Acad. Sci. USA 32 (1946), 331-332, https://doi.org/10.1073/pnas.32.12.331; formalized in Mathlib as `Behrend.roth_lower_bound` (Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean), whose explicit constant this statement reproduces. Cited on Erdős Problem #142, https://www.erdosproblems.com/142 (cited there as [Er80, p.92], [Er81, p.4], [Er97c], [Va99, 1.27])

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos142

theorem behrend_lower_bound (N : ℕ) :
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤ (r 3 N : ℝ) := by sorry

end Erdos142
