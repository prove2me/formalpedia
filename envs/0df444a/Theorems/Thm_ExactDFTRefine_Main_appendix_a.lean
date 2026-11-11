-- Prove2me | Theorems.Thm_ExactDFTRefine_Main_appendix_a
-- name    : ExactDFTRefine.Main.appendix_a
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:01:54.053184+00:00
-- url     : https://prove2.me/theorems/003a608e-4bea-4695-bde4-2e9152673e9e
-- title:
--   Appendix A — S_N(x) ≤ e^x ≤ U_N(x) for N ≥ 1 and 0 ≤ x ≤ 1
-- statement:
--   For $N \ge 1$ let $S_N(x) = \sum_{j=0}^{N-1} x^j/j!$ and $U_N(x) = S_N(x) + \frac{N+1}{N\,N!}x^N$. For every $0 \le x \le 1$,
--   $$S_N(x) \le e^x \le U_N(x).$$
--   These bounds certify the logarithm enclosures of Table 2: an upper bound $\ell_r$ on $\log(145/r)$ is certified by $145/r \le S_N(\ell_r)$, and a lower one by $U_N(\ell_r/8)^8 \le 145/r$.
--
--   Differences from the source: none.
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 8, Appendix A

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

/-- **Appendix A**, p. 8. For `N ≥ 1` and `0 ≤ x ≤ 1`: `S_N(x) ≤ e^x ≤ U_N(x)`, where
`S_N(x) = ∑_{j=0}^{N-1} x^j/j!` and `U_N(x) = S_N(x) + ((N + 1)/(N N!)) x^N`. -/
theorem appendix_a (N : ℕ) (hN : 1 ≤ N) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    SN N x ≤ Real.exp x ∧ Real.exp x ≤ UN N x := by sorry

end ExactDFTRefine.Main
