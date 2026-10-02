-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_dir_deriv_eq_finite_diff_l_convex
-- name    : DiscreteConvex.LConvexFunctionsD.dir_deriv_eq_finite_diff_l_convex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:06:00.400375+00:00
-- url     : https://prove2.me/theorems/c2b810c2-420d-44cf-85b3-bf162ad19ebb
-- title:
--   Proposition 7.44 -- dir_deriv_eq_finite_diff_l_convex
-- statement:
--   **Proposition 7.44** (p.197). For $g\in L[\mathbb Z|\mathbb R\to\mathbb R]$ and $p\in\operatorname{dom}_{\mathbb R} g\cap\mathbb Z^V$, we have $g'(p;\chi_X) = g(p+\chi_X)-g(p)$ for $X\subseteq V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.197, Proposition 7.44.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.197, Proposition 7.44

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexIntegralR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DirDeriv

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.44 (p.197). Consistency of the directional derivative with the finite
difference for `L[Z|R→R]` at an integer point. -/
theorem dir_deriv_eq_finite_diff_l_convex (g : (V → ℝ) → WithTop ℝ) (hg : LConvexIntegralR g)
    (p : V → ℝ) (hp : p ∈ DomR g) (hpZ : ∀ v, ∃ k : ℤ, p v = (k : ℝ)) (X : Finset V) :
    DirDeriv g p (fun v => if v ∈ X then (1 : ℝ) else 0) =
      g (fun v => p v + (if v ∈ X then (1 : ℝ) else 0)) - g p := by sorry

end DiscreteConvex.LConvexFunctionsD
