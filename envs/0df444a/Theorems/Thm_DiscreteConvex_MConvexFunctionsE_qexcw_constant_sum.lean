-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_qexcw_constant_sum
-- name    : DiscreteConvex.MConvexFunctionsE.qexcw_constant_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:08:39.256982+00:00
-- url     : https://prove2.me/theorems/1d929edf-fd9c-4d2f-9cc4-e9b3ecdb28af
-- title:
--   Proposition 6.70 -- qexcw_constant_sum
-- statement:
--   **Proposition 6.70** (p.171). For a set $B\subseteq\mathbb Z^V$ satisfying (Q-EXCw), we have $x(V)=y(V)$ for any $x,y\in B$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.171, Proposition 6.70.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.171, Proposition 6.70

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QEXCw

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.70 (p.171). A (Q-EXCw) set has constant coordinate sum. -/
theorem qexcw_constant_sum (B : Set (V → ℤ)) (hB : QEXCw B) :
    ∀ x ∈ B, ∀ y ∈ B, ∑ v, x v = ∑ v, y v := by sorry

end DiscreteConvex.MConvexFunctionsE
