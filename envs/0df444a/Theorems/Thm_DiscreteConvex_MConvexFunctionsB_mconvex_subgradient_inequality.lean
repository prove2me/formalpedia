-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsB_mconvex_subgradient_inequality
-- name    : DiscreteConvex.MConvexFunctionsB.mconvex_subgradient_inequality
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:10:42.803703+00:00
-- url     : https://prove2.me/theorems/49db9f24-1e42-4043-b379-ba0ed4e8b27b
-- title:
--   Proposition 6.25 -- mconvex_subgradient_inequality
-- statement:
--   **Proposition 6.25** (p.148), Eq. (6.54)-(6.55). For an M-convex function $f$ and $x,y \in \operatorname{dom} f$, $f(y) \ge f(x) + \check f(x,y)$, where $\check f(x,y)$ is the infimum, over nonnegative-integer flows $\lambda_{uv}$ routing $y-x$ as a combination of exchange steps $\chi_v-\chi_u$, of the total exchange cost $\sum_{u,v}\lambda_{uv}[f(x-\chi_u+\chi_v)-f(x)]$: a discrete subgradient inequality.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.148, Proposition 6.25, Eq. (6.54)-(6.55).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.148, Proposition 6.25

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_FCheck

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.148, Proposition 6.25, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Proposition 6.25 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.148). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_subgradient_inequality {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (x y : V → ℤ) (hx : x ∈ DomZ f)
    (hy : y ∈ DomZ f) :
    f y ≥ f x + FCheck f x y := by sorry

end DiscreteConvex.MConvexFunctionsB
