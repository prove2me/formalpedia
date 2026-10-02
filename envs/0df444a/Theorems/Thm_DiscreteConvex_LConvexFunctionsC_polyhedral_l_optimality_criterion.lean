-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsC_polyhedral_l_optimality_criterion
-- name    : DiscreteConvex.LConvexFunctionsC.polyhedral_l_optimality_criterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:40:41.223515+00:00
-- url     : https://prove2.me/theorems/8a61528c-16ac-41df-aed5-64ac58cfeb45
-- title:
--   Theorem 7.33 -- polyhedral_l_optimality_criterion
-- statement:
--   **Theorem 7.33** (L-optimality criterion; p.193). GOAL. (1) For a polyhedral L-convex function $g\in L[\mathbb R\to\mathbb R]$ and $p\in\operatorname{dom}_{\mathbb R} g$: $g(p)\le g(q)$ for all $q$ iff $g'(p;\chi_Y)\ge 0$ for all $Y\subseteq V$ and $g'(p;\mathbf 1)=0$. (2) For a polyhedral L$^\natural$-convex function $g\in L^\natural[\mathbb R\to\mathbb R]$ and $p\in\operatorname{dom}_{\mathbb R} g$: $g(p)\le g(q)$ for all $q$ iff $g'(p;\pm\chi_Y)\ge 0$ for all $Y\subseteq V$.
--
--   The polyhedral analogue of the L-optimality criterion (Theorem 7.14, formalized in mission `08-lconvex-functions-i`) and the direct L-side mirror of mission `24-ch06d-mconvexfunctions`'s M-optimality criterion (Theorem 6.52): global optimality of a polyhedral L-(natural-)convex function reduces to checking finitely many directional derivatives.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.193, Theorem 7.33.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.193, Theorem 7.33

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNaturalConvexR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DirDeriv
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsPolyhedralConvex

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.33 (L-optimality criterion; p.193). GOAL. Global optimality of a polyhedral L-convex
or L♮-convex function is characterized by directional derivatives along coordinate-subset
indicators. Polyhedrality is the book's standing hypothesis and is not implied by (SBF[R]) and
(TRF[R]): `DirDeriv` is a `WithTop` infimum of difference quotients and reads the junk value `0`
when they are unbounded below, which `g(p) = -√(1 - (p₁ - p₂)²)` exploits at `p = (-1, 0)`. -/
theorem polyhedral_l_optimality_criterion (g : (V → ℝ) → WithTop ℝ)
    (hpoly : IsPolyhedralConvex g) (p : V → ℝ) (hp : p ∈ DomR g) :
    ((SBFR g ∧ TRFR g) →
      ((∀ q, g p ≤ g q) ↔
        ((∀ Y : Finset V, DirDeriv g p (fun v => if v ∈ Y then (1 : ℝ) else 0) ≥ 0) ∧
          DirDeriv g p (fun _ => (1 : ℝ)) = 0))) ∧
    (LNaturalConvexR g →
      ((∀ q, g p ≤ g q) ↔
        (∀ Y : Finset V, DirDeriv g p (fun v => if v ∈ Y then (1 : ℝ) else 0) ≥ 0 ∧
          DirDeriv g p (fun v => if v ∈ Y then (-1 : ℝ) else 0) ≥ 0))) := by sorry

end DiscreteConvex.LConvexFunctionsC
