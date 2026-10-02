-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsB_mconvex_descent_direction
-- name    : DiscreteConvex.MConvexFunctionsB.mconvex_descent_direction
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:10:14.095403+00:00
-- url     : https://prove2.me/theorems/d4bc5dd3-0447-4d95-9ac1-0d85d4c24865
-- title:
--   Proposition 6.23 -- mconvex_descent_direction
-- statement:
--   **Proposition 6.23** (p.147), Eq. (6.50). For an M-convex function $f$ and $x,y \in \operatorname{dom} f$ with $f(x) > f(y)$, $f(x) > \min_{u \in \operatorname{supp}^+(x-y)} \min_{v \in \operatorname{supp}^-(x-y)} f(x-\chi_u+\chi_v)$: a suboptimal point always has a strict single-exchange descent direction.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.147, Proposition 6.23, Eq. (6.50).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.147, Proposition 6.23

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_CharVec

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.147, Proposition 6.23, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Proposition 6.23 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.147). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_descent_direction {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (x y : V → ℤ) (hx : x ∈ DomZ f)
    (hy : y ∈ DomZ f) (hgt : f x > f y) :
    f x > (SuppPos x y).inf (fun u => (SuppNeg x y).inf (fun v =>
      f (fun w => x w - CharVec u w + CharVec v w))) := by sorry

end DiscreteConvex.MConvexFunctionsB
