-- Prove2me | Theorems.Thm_DissolveCDF_proposition_3_9
-- name    : DissolveCDF.proposition_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:32:14.83863+00:00
-- url     : https://prove2.me/theorems/c4800cd3-9ff3-41ab-8000-2a2368b7328c
-- title:
--   Proposition 3.9 — stationary points of OCP and of CDF on $\mathcal M$ coincide
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ is the objective and $c:\mathbb R^n\to\mathbb R^p$ the constraint map of the problem (OCP) $\min_x f(x)$ s.t. $c(x)=0$, with feasible set $\mathcal M=\{x: c(x)=0\}$; $\mathcal A:\mathbb R^n\to\mathbb R^n$ is a constraint dissolving operator, and $f,c,\mathcal A$ satisfy Assumptions 1.1 and 1.2.
--
--   For every penalty parameter $\beta\in\mathbb R$:
--
--   1. every first-order stationary point of OCP is a first-order stationary point of CDF;
--   2. every first-order stationary point of CDF that lies in $\mathcal M$ is a first-order stationary point of OCP.
--
--   Here a stationary point of OCP satisfies (2.1) and a stationary point of CDF satisfies $\nabla h(x)=0$.
--
--   Differences from the source: none.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, Proposition 3.9, p.11 (proof Appendix A.2.1, p.22)

import Mathlib
import Definitions.Def_DissolveCDF_Assumption11
import Definitions.Def_DissolveCDF_Assumption12
import Definitions.Def_DissolveCDF_IsStationaryOCP
import Definitions.Def_DissolveCDF_IsStationaryCDF

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Proposition 3.9, p.11 (proof p.22): any first-order stationary point of OCP is a
first-order stationary point of CDF (for every penalty parameter `β`). On the other hand, any
first-order stationary point of CDF over `M` is a first-order stationary point of OCP.

Under the blanket Assumptions 1.1 and 1.2 (`h11`, `h12`). -/
theorem proposition_3_9 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p)}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h11 : Assumption11 f c) (h12 : Assumption12 c A) :
    (∀ (β : ℝ) (y : EuclideanSpace ℝ (Fin n)), IsStationaryOCP f c y → IsStationaryCDF f c A β y) ∧
      (∀ (β : ℝ) (y : EuclideanSpace ℝ (Fin n)), c y = 0 → IsStationaryCDF f c A β y →
        IsStationaryOCP f c y) := by sorry

end DissolveCDF
