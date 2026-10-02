-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsB_local_submodularity
-- name    : DiscreteConvex.LConvexFunctionsB.local_submodularity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:24:18.972538+00:00
-- url     : https://prove2.me/theorems/c21da859-4d1e-40c9-8229-fa9663cbb035
-- title:
--   Proposition 7.5 -- local_submodularity
-- statement:
--   **Proposition 7.5** (Local submodularity; p.180). Let $g:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ have L$^\natural$-convex effective domain. Then $g$ satisfies the submodularity inequality for all $p,q\in\mathbb Z^V$ iff it satisfies it for all $p,q$ with $\|p-q\|_\infty=1$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, Proposition 7.5.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, Proposition 7.5

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNatConvexSet

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.5 (Local submodularity; p.180). Submodularity of `g` (with `dom g` L♮-convex)
is a local property, needing only pairs at `L∞`-distance 1. -/
theorem local_submodularity (g : (V → ℤ) → WithTop ℝ) (hdom : LNatConvexSet (DomZ g)) :
    (∀ p q : V → ℤ, g p + g q ≥ g (fun v => max (p v) (q v)) + g (fun v => min (p v) (q v))) ↔
    (∀ p q : V → ℤ, (∀ v, |p v - q v| ≤ 1) →
      g p + g q ≥ g (fun v => max (p v) (q v)) + g (fun v => min (p v) (q v))) := by sorry

end DiscreteConvex.LConvexFunctionsB
