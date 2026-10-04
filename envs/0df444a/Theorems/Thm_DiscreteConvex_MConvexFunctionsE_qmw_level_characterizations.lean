-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_qmw_level_characterizations
-- name    : DiscreteConvex.MConvexFunctionsE.qmw_level_characterizations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:09:48.607711+00:00
-- url     : https://prove2.me/theorems/96b0688f-d21b-402a-baf3-c1da5ebacff0
-- title:
--   Theorem 6.67 -- qmw_level_characterizations
-- statement:
--   **Theorem 6.67** (p.170). For $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$, (QMw) is equivalent to each of: (6.93) $\max\{f(x),f(y)\}\ge\min_{u,v}\min\{f(x-\chi_u+\chi_v),f(y+\chi_u-\chi_v)\}$ for distinct $x,y\in\operatorname{dom} f$; (6.94) $f(x)\ge\min_{u,v}f(x-\chi_u+\chi_v)$ for distinct $x,y\in\operatorname{dom} f$ with $f(x)\ge f(y)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.170, Theorem 6.67.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.170, Theorem 6.67

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MinDown
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MinDownSym

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.67 (p.170). Level-set characterizations of (QMw). -/
theorem qmw_level_characterizations (f : (V → ℤ) → WithTop ℝ) :
    [QMw f,
     ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, x ≠ y → max (f x) (f y) ≥ MinDownSym f x y,
     ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, x ≠ y → f x ≥ f y → f x ≥ MinDown f x y].TFAE := by sorry

end DiscreteConvex.MConvexFunctionsE
