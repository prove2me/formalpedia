-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsB_l_convex_translation_inequality
-- name    : DiscreteConvex.LConvexFunctionsB.l_convex_translation_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:22:15.006889+00:00
-- url     : https://prove2.me/theorems/1dc34f44-80c3-4e38-a21b-bf39d8e99c42
-- title:
--   Theorem 7.2 -- l_convex_translation_inequality
-- statement:
--   **Theorem 7.2** (p.178). An L-convex function $g\in L[\mathbb Z\to\mathbb R]$ satisfies $g(p)+g(q)\ge g((p-\alpha\mathbf 1)\vee q)+g(p\wedge(q+\alpha\mathbf 1))$ for all $p,q\in\mathbb Z^V$ and $\alpha\in\mathbb Z$ (both signs of $\alpha$, strengthening (SBF$^\natural$[Z])'s $\alpha\ge 0$ restriction).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, Theorem 7.2.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, Theorem 7.2

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.2 (p.178). A strengthening of (SBF♮[Z]) to arbitrary `α ∈ Z`. -/
theorem l_convex_translation_inequality (g : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g) :
    ∀ p q : V → ℤ, ∀ alpha : ℤ,
      g p + g q ≥ g (fun v => max (p v - alpha) (q v)) + g (fun v => min (p v) (q v + alpha)) := by sorry

end DiscreteConvex.LConvexFunctionsB
