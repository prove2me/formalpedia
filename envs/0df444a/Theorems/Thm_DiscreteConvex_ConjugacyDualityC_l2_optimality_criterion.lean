-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityC_l2_optimality_criterion
-- name    : DiscreteConvex.ConjugacyDualityC.l2_optimality_criterion
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:45:21.447101+00:00
-- url     : https://prove2.me/theorems/7431aa53-05d5-4dfc-bb44-21ed61041892
-- title:
--   Theorem 8.43 -- l2_optimality_criterion
-- statement:
--   **Theorem 8.43** (L2-optimality criterion; p.232). For an L2-convex function $g$ and $p\in\operatorname{dom} g$: $p$ globally minimizes $g$ iff $g(p)\le g(p+\chi_Y)$ for all $Y\subseteq V$ and $g(p)=g(p+\mathbf 1)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.232, Theorem 8.43.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.232, Theorem 8.43

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2Convex

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.43 (L2-optimality criterion; p.232). Global optimality of an L2-convex function is
characterized by local non-improvement plus periodicity. -/
theorem l2_optimality_criterion (g : (V → ℤ) → WithTop ℝ) (hg : L2Convex g) (p : V → ℤ)
    (hp : p ∈ DomZ g) :
    (∀ q, g p ≤ g q) ↔
      ((∀ Y : Finset V, g p ≤ g (fun v => p v + IndicatorVec Y v)) ∧ g p = g (p + 1)) := by sorry

end DiscreteConvex.ConjugacyDualityC
