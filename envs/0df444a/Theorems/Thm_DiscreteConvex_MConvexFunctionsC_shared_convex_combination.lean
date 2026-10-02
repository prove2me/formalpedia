-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsC_shared_convex_combination
-- name    : DiscreteConvex.MConvexFunctionsC.shared_convex_combination
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:39:12.491305+00:00
-- url     : https://prove2.me/theorems/b2fed403-32d0-4815-a1b0-f5f3d0ac0b1c
-- title:
--   Theorem 6.44 -- shared_convex_combination
-- statement:
--   **Theorem 6.44** (p.159-160), Eq. (6.71)-(6.72). For two M$^\natural$-convex functions $f_1,f_2$ and $x\in\mathbb R^V$, there is a single set of convex-combination coefficients $\lambda=(\lambda_y : y\in N(x))$ over the integral neighborhood of $x$ that simultaneously represents both $\bar f_1(x)$ and $\bar f_2(x)$ as the corresponding weighted sum of $f_1$ (resp. $f_2$) values at the same points $y$. This shared-coefficient fact, though technical, is crucial for the M$^\natural$ separation theorem of Chapter 8.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.159-160, Theorem 6.44, Eq. (6.71)-(6.72).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.159-160, Theorem 6.44

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IntegralNeighborhoodFinset
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureVal

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.44 (p.159-160). -/
theorem shared_convex_combination (f1 f2 : (V → ℤ) → WithTop ℝ) (hf1 : MNaturalConvex f1)
    (hf2 : MNaturalConvex f2) (x : V → ℝ) :
    ∃ lam : (V → ℤ) → ℝ,
      (∀ y ∈ IntegralNeighborhoodFinset x, 0 ≤ lam y) ∧
      (∑ y ∈ IntegralNeighborhoodFinset x, lam y = 1) ∧
      (∀ v, ∑ y ∈ IntegralNeighborhoodFinset x, lam y * (y v : ℝ) = x v) ∧
      ConvexClosureVal f1 x =
        ((∑ y ∈ IntegralNeighborhoodFinset x, lam y * (f1 y).untopD 0 : ℝ) : WithTop ℝ) ∧
      ConvexClosureVal f2 x =
        ((∑ y ∈ IntegralNeighborhoodFinset x, lam y * (f2 y).untopD 0 : ℝ) : WithTop ℝ) := by sorry

end DiscreteConvex.MConvexFunctionsC
