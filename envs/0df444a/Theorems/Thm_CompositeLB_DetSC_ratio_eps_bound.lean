-- Prove2me | Theorems.Thm_CompositeLB_DetSC_ratio_eps_bound
-- name    : CompositeLB.DetSC.ratio_eps_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:25:16.83848+00:00
-- url     : https://prove2.me/theorems/de06f945-e367-4ac9-a531-d3a382e7e77a
-- title:
--   Appendix B.4, p. 18 — the choice of rounds reaches ε/ε₀
-- statement:
--   Let $Q>1$, $\epsilon,\epsilon_0>0$, and $2\sqrt Q\,\epsilon\le\epsilon_0$. Choose the nonnegative integer
--
--   $$t=\left\lfloor\frac{\sqrt Q-1}{4}\log\!\left(\frac{\epsilon_0}{2\sqrt Q\,\epsilon}\right)\right\rfloor.$$
--
--   Then $\frac{1}{2\sqrt Q}\exp(-4t/(\sqrt Q-1))\ge\epsilon/\epsilon_0$. This identifies a round threshold at which the normalized objective gap remains large enough.
--
--   **Formalization Note** The bound on $\epsilon_0$ makes the logarithm nonnegative, so Nat.floor matches the page's ordinary floor rather than Lean's zero value on a negative argument.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, App. B.4, p. 18, display beginning ‘and when t’

import Mathlib
import Definitions.Def_CompositeLB_DetSC_HardInstance

namespace CompositeLB.DetSC

/-- Appendix B.4, p. 18: the chosen number of rounds makes the gap at least ε/ε₀. -/
theorem ratio_eps_bound (Q eps eps0 : ℝ) (hQ : 1 < Q)
    (heps : 0 < eps) (heps0 : 0 < eps0)
    (hlarge : 2 * Real.sqrt Q * eps ≤ eps0)
    (t : ℕ)
    (ht : t = Nat.floor ((Real.sqrt Q - 1) / 4 *
      Real.log (eps0 / (2 * Real.sqrt Q * eps)))) :
    1 / (2 * Real.sqrt Q) *
        Real.exp (-4 * (t : ℝ) / (Real.sqrt Q - 1)) ≥ eps / eps0 := by sorry

end CompositeLB.DetSC
