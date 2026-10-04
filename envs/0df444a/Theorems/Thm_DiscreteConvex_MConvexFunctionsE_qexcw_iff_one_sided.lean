-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_qexcw_iff_one_sided
-- name    : DiscreteConvex.MConvexFunctionsE.qexcw_iff_one_sided
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:08:27.499987+00:00
-- url     : https://prove2.me/theorems/c9b8693a-f340-4e44-8466-9d01c83b4456
-- title:
--   Proposition 6.69 -- qexcw_iff_one_sided
-- statement:
--   **Proposition 6.69** (p.171). A set $B\subseteq\mathbb Z^V$ satisfies (Q-EXCw) if and only if, for distinct $x,y\in B$, there exist $u\in\operatorname{supp}^+(x-y)$ and $v\in\operatorname{supp}^-(x-y)$ with $x-\chi_u+\chi_v\in B$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.171, Proposition 6.69.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.171, Proposition 6.69

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QEXCw

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.69 (p.171). (Q-EXCw) needs only the one-sided conclusion. -/
theorem qexcw_iff_one_sided (B : Set (V → ℤ)) :
    QEXCw B ↔ ∀ x ∈ B, ∀ y ∈ B, x ≠ y → ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
      (fun w => x w - CharVec u w + CharVec v w) ∈ B := by sorry

end DiscreteConvex.MConvexFunctionsE
