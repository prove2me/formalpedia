-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlowsC_unique_min_gives_equality
-- name    : DiscreteConvex.NetworkFlowsC.unique_min_gives_equality
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T03:11:07.937259+00:00
-- url     : https://prove2.me/theorems/58810e10-4eeb-4c1b-b230-8118fd02e531
-- title:
--   Proposition 9.23 -- unique_min_gives_equality
-- statement:
--   **Proposition 9.23** (p.266). Let $f$ be M-convex, $x\in\operatorname{dom}_{\mathbb Z}f$, $y\in\mathbb Z^V$ with $\|x-y\|_\infty=1$. If $(x,y)$ satisfies the unique-min condition, then $y\in\operatorname{dom}_{\mathbb Z}f$ and $f(y)-f(x)=\check f(x,y)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, Proposition 9.23.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, Proposition 9.23

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_DomZ
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_NetworkFlowsC_UniqueMinConditionPair
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MinWeightValuePair

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Proposition 9.23 (p.266). For an M-convex `f`, `x ∈ dom_Z f`, `y` with `‖x-y‖∞ = 1`, if
`(x,y)` satisfies the unique-min condition then `y ∈ dom_Z f` and `f(y)-f(x) = ˇf(x,y)`. -/
theorem unique_min_gives_equality (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (x y : V → ℤ)
    (hx : x ∈ DomZ f) (hnorm : (∀ v, x v - y v ≤ 1 ∧ y v - x v ≤ 1) ∧ ∃ v, x v ≠ y v)
    (hUM : UniqueMinConditionPair f x y) :
    y ∈ DomZ f ∧ f y - f x = MinWeightValuePair f x y := by sorry

end DiscreteConvex.NetworkFlowsC
