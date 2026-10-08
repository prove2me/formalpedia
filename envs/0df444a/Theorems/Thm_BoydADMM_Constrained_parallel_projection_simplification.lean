-- Prove2me | Theorems.Thm_BoydADMM_Constrained_parallel_projection_simplification
-- name    : BoydADMM.Constrained.parallel_projection_simplification
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:20:12.666498+00:00
-- url     : https://prove2.me/theorems/27edab00-a25c-485f-b5ff-5153ac257883
-- title:
--   Parallel projection ADMM reduces to project-and-average
-- statement:
--   Let $N\ge1$ and $\rho>0$, and let $\mathcal A_1,\ldots,\mathcal A_N\subseteq\mathbb R^n$ be nonempty closed convex sets. Start the parallel projection ADMM iteration from arbitrary $z^0$ and $u_i^0$. Then the average dual variable vanishes after every update, $\bar u^{k+1}=0$ for $k\ge0$, and $z^{k+1}=\bar x^{k+1}$ for $k\ge1$. From $k\ge2$ the same run therefore satisfies
--
--   $$x_i^{k+1}=\Pi_{\mathcal A_i}(\bar x^k-u_i^k),\qquad u_i^{k+1}=u_i^k+(x_i^{k+1}-\bar x^{k+1})\qquad(i=1,\ldots,N).$$
--
--   If $\bar u^0=0$, these two simplified updates already hold for every $k\ge1$. Thus the simplified algorithm describes the iterates of the displayed three-update method, with its initial step and index ranges made explicit.
--
--   **Formalization Note** Projection is relational and the theorem ranges over every run; it does not assume the vanishing dual average. The book's intermediate formula prints $-z^k$ where the iteration requires $-z^{k+1}$. It also says the first step projects onto the sets $\mathcal C_i$; these are the $\mathcal A_i$ of §5.1.2.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 36, §5.1.2, parallel-projection simplification; https://doi.org/10.1561/2200000016

import Mathlib
import Definitions.Def_BoydADMM_Constrained_Run

namespace BoydADMM.Constrained

/-- §5.1.2, p. 36: every parallel projection ADMM run reduces to project-and-average
after its dual average has vanished. The index ranges keep the arbitrary initial state. -/
theorem parallel_projection_simplification {N n : ℕ} (hN : 0 < N)
    (A : Fin N → Set (Vec n))
    (hAne : ∀ i, (A i).Nonempty) (hAclosed : ∀ i, IsClosed (A i))
    (hAconvex : ∀ i, Convex ℝ (A i))
    (ρ : ℝ) (hρ : 0 < ρ)
    (x : ℕ → Blocks N n) (z : ℕ → Vec n) (u : ℕ → Blocks N n)
    (hrun : IsParallelRun A x z u) :
    (∀ k, avg (u (k + 1)) = 0) ∧
    (∀ k, 1 ≤ k → z (k + 1) = avg (x (k + 1))) ∧
    (∀ k, 2 ≤ k → ∀ i,
      RandomGradFree.Nonsmooth.IsMetricProjection (A i)
        (avg (x k) - u k i) (x (k + 1) i) ∧
      u (k + 1) i = u k i + (x (k + 1) i - avg (x (k + 1)))) ∧
    (avg (u 0) = 0 → ∀ k, 1 ≤ k → ∀ i,
      RandomGradFree.Nonsmooth.IsMetricProjection (A i)
        (avg (x k) - u k i) (x (k + 1) i) ∧
      u (k + 1) i = u k i + (x (k + 1) i - avg (x (k + 1)))) := by sorry

end BoydADMM.Constrained
