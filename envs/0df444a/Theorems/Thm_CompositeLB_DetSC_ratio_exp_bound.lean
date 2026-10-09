-- Prove2me | Theorems.Thm_CompositeLB_DetSC_ratio_exp_bound
-- name    : CompositeLB.DetSC.ratio_exp_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:25:40.128982+00:00
-- url     : https://prove2.me/theorems/bd9e8ec3-1f4a-4500-91f7-ffe99483e1ca
-- title:
--   Appendix B.4, p. 18 — ceiling choice and exponential ratio bound
-- statement:
--   Let $Q>1$, $q=(\sqrt Q-1)/(\sqrt Q+1)$, and let nonnegative integers $t,k$ satisfy $k+1=\lceil t-1/(2\log q)\rceil$. Then
--
--   $$\frac{q^{2t}-q^{2k+2}}{\sqrt Q}\ge\frac{q^{2t}}{2\sqrt Q}\ge\frac{1}{2\sqrt Q}\exp\!\left(-\frac{4t}{\sqrt Q-1}\right).$$
--
--   This turns the chain's geometric decay into a bound expressed in completed rounds.
--
--   **Formalization Note** The hypotheses give $0<q<1$, so $\log q<0$ and the ceiling has its intended meaning. The ceiling is an integer, matching $k+1$.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, App. B.4, p. 18, opening display

import Mathlib
import Definitions.Def_CompositeLB_DetSC_HardInstance

namespace CompositeLB.DetSC

/-- Appendix B.4, p. 18: the ceiling choice of `k` yields an exponential gap. -/
theorem ratio_exp_bound (Q q : ℝ) (hQ : 1 < Q)
    (hq : q = (Real.sqrt Q - 1) / (Real.sqrt Q + 1))
    (t k : ℕ)
    (hk : (k : ℤ) + 1 = ⌈(t : ℝ) - 1 / (2 * Real.log q)⌉) :
    (q ^ (2 * t) - q ^ (2 * k + 2)) / Real.sqrt Q ≥
        q ^ (2 * t) / (2 * Real.sqrt Q) ∧
      q ^ (2 * t) / (2 * Real.sqrt Q) ≥
        1 / (2 * Real.sqrt Q) *
          Real.exp (-4 * (t : ℝ) / (Real.sqrt Q - 1)) := by sorry

end CompositeLB.DetSC
