-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsD_polyhedral_mnat_convex_supermodular
-- name    : DiscreteConvex.MConvexFunctionsD.polyhedral_mnat_convex_supermodular
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:55:53.75058+00:00
-- url     : https://prove2.me/theorems/800dbb7a-7eaf-4ae9-b3f1-60d4a99a9ad4
-- title:
--   Theorem 6.51 -- polyhedral_mnat_convex_supermodular
-- statement:
--   **Theorem 6.51** (p.163). A polyhedral M$^\natural$-convex function $f\in M^\natural[\mathbb R\to\mathbb R]$ is supermodular: $f(x)+f(y)\le f(x\vee y)+f(x\wedge y)$ for all $x,y\in\mathbb R^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Theorem 6.51.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Theorem 6.51

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MNaturalConvexR

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.51 (p.182). -/
theorem polyhedral_mnat_convex_supermodular (f : (V → ℝ) → WithTop ℝ) (hf : MNaturalConvexR f) :
    ∀ x y : V → ℝ, f x + f y ≤ f (fun v => max (x v) (y v)) + f (fun v => min (x v) (y v)) := by sorry

end DiscreteConvex.MConvexFunctionsD
