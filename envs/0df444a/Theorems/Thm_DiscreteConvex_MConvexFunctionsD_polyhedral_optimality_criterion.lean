-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsD_polyhedral_optimality_criterion
-- name    : DiscreteConvex.MConvexFunctionsD.polyhedral_optimality_criterion
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:56:28.986007+00:00
-- url     : https://prove2.me/theorems/9944985e-3bd9-4dae-8417-5f11b670db3b
-- title:
--   Theorem 6.52 -- polyhedral_optimality_criterion
-- statement:
--   **Theorem 6.52** (M-optimality criterion; p.182). (1) For a polyhedral M-convex function $f$ and $x\in\operatorname{dom}_{\mathbb R} f$, $f(x)\le f(y)\ \forall y \iff f'(x;-\chi_u+\chi_v)\ge 0\ \forall u,v$. (2) The M$^\natural$ analogue adds $f'(x;\pm\chi_v)\ge 0\ \forall v$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Theorem 6.52.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Theorem 6.52

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MNaturalConvexR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DirDeriv

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.52 (M-optimality criterion; p.182), stated for **polyhedral** M-convex functions,
the page's class `M[R→R]`. `DirDeriv` is a `WithTop` infimum of difference quotients and returns
`0` when they are unbounded below, so without polyhedrality the criterion is refuted by
`f(x) = φ(x₁)` on the line `x₁ + x₂ = 0` with `φ(t) = -√(1-t²)` on `[-1,1]` and `+∞` elsewhere:
at `x = (-1,1)` the function is not minimal while both directional derivatives pass the test. -/
theorem polyhedral_optimality_criterion (f : (V → ℝ) → WithTop ℝ) (hpoly : IsPolyhedralConvex f)
    (x : V → ℝ) (hx : x ∈ DomR f) :
    (MExchangeAxiomR f →
      ((∀ y, f x ≤ f y) ↔ ∀ u v : V, DirDeriv f x (fun w => (CharVec v w - CharVec u w : ℝ)) ≥ 0)) ∧
    (MNaturalConvexR f →
      ((∀ y, f x ≤ f y) ↔
        (∀ u v : V, DirDeriv f x (fun w => (CharVec v w - CharVec u w : ℝ)) ≥ 0) ∧
        (∀ v : V, DirDeriv f x (fun w => (CharVec v w : ℝ)) ≥ 0 ∧
          DirDeriv f x (fun w => (-(CharVec v w : ℝ))) ≥ 0))) := by sorry

end DiscreteConvex.MConvexFunctionsD
