-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_integral_mconvex_iff_integral_argmin
-- name    : DiscreteConvex.MConvexFunctionsE.integral_mconvex_iff_integral_argmin
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:12:34.66601+00:00
-- url     : https://prove2.me/theorems/fc720f3d-740f-41a3-a43b-fec8f4e43290
-- title:
--   Theorem 6.64 -- integral_mconvex_iff_integral_argmin
-- statement:
--   **Theorem 6.64** (p.168). For a polyhedral convex function $f:\mathbb R^V\to\mathbb R\cup\{+\infty\}$ with $\operatorname{dom}_{\mathbb R} f\ne\emptyset$: (a) $f\in M[\mathbb Z|\mathbb R\to\mathbb R]$ iff (d) $\arg\min f[-p]\in M_0[\mathbb Z|\mathbb R]$ for every $p\in\mathbb R^V$ with $\arg\min f[-p]$ nonempty. The integral refinement of Theorem 6.63's (a)$\Leftrightarrow$(d).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.168, Theorem 6.64.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.168, Theorem 6.64

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_ArgMinOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_LinearWeightR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MConvexIntegralR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsMZeroZR

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.64 (p.168). The integral refinement of Theorem 6.63's (a) ⇔ (d), for the same polyhedral class. -/
theorem integral_mconvex_iff_integral_argmin (f : (V → ℝ) → WithTop ℝ)
    (hpoly : IsPolyhedralConvex f) (hdom : (DomR f).Nonempty) :
    MConvexIntegralR f ↔
      ∀ p : V → ℝ, (ArgMinOn (LinearWeightR f (fun v => -p v))).Nonempty →
        IsMZeroZR (ArgMinOn (LinearWeightR f (fun v => -p v))) := by sorry

end DiscreteConvex.MConvexFunctionsE
