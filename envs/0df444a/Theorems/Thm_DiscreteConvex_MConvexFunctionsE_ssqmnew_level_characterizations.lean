-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_ssqmnew_level_characterizations
-- name    : DiscreteConvex.MConvexFunctionsE.ssqmnew_level_characterizations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:11:43.113981+00:00
-- url     : https://prove2.me/theorems/e7224bcd-f7bf-46f8-b2c7-deac83bbadd9
-- title:
--   Theorem 6.75 -- ssqmnew_level_characterizations
-- statement:
--   **Theorem 6.75** (p.173). For $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$, (SSQM$\ne_w$) is equivalent to each of: (6.96) $\max\{f(x),f(y)\}>\min_{u,v}\min\{f(x-\chi_u+\chi_v),f(y+\chi_u-\chi_v)\}$ for $x,y\in\operatorname{dom} f$ with $f(x)\ne f(y)$; (6.97) $f(x)>\min_{u,v}f(x-\chi_u+\chi_v)$ for $x,y\in\operatorname{dom} f$ with $f(x)>f(y)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.173, Theorem 6.75.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.173, Theorem 6.75

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMNeW
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MinDown
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MinDownSym

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.75 (p.173). Level-set characterizations of (SSQM≠_w). -/
theorem ssqmnew_level_characterizations (f : (V → ℤ) → WithTop ℝ) :
    [SSQMNeW f,
     ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, f x ≠ f y → max (f x) (f y) > MinDownSym f x y,
     ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, f x > f y → f x > MinDown f x y].TFAE := by sorry

end DiscreteConvex.MConvexFunctionsE
