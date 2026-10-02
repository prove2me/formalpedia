-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_integral_lconvex_iff_integral_argmin
-- name    : DiscreteConvex.LConvexFunctionsD.integral_lconvex_iff_integral_argmin
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:06:13.210851+00:00
-- url     : https://prove2.me/theorems/90f5aee4-5d15-4204-af04-46b16bb0fd54
-- title:
--   Theorem 7.46 -- integral_lconvex_iff_integral_argmin
-- statement:
--   **Theorem 7.46** (p.198). For a polyhedral convex function $g:\mathbb R^V\to\mathbb R\cup\{+\infty\}$ with $\operatorname{dom}_{\mathbb R} g\ne\emptyset$: $g\in L[\mathbb Z|\mathbb R\to\mathbb R]$ iff $\arg\min g[-x]\in L_0[\mathbb Z|\mathbb R]$ for every $x$ with $\arg\min g[-x]$ nonempty. The integral refinement of Theorem 7.45's (a) $\Leftrightarrow$ (d).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.198, Theorem 7.46.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.198, Theorem 7.46

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegralPolyhedron
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ArgMinR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexIntegralR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexPolyhedron

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.46 (p.198). The integral refinement of Theorem 7.45's (a) ⇔ (d). -/
theorem integral_lconvex_iff_integral_argmin (g : (V → ℝ) → WithTop ℝ) (hdom : (DomR g).Nonempty) :
    LConvexIntegralR g ↔
      ∀ x : V → ℝ, (ArgMinR (LinearWeightR g (fun v => - x v))).Nonempty →
        (LConvexPolyhedron (ArgMinR (LinearWeightR g (fun v => - x v))) ∧
          IsIntegralPolyhedron (ArgMinR (LinearWeightR g (fun v => - x v)))) := by sorry

end DiscreteConvex.LConvexFunctionsD
