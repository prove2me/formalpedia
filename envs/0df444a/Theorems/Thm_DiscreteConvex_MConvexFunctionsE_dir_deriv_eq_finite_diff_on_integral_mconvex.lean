-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_dir_deriv_eq_finite_diff_on_integral_mconvex
-- name    : DiscreteConvex.MConvexFunctionsE.dir_deriv_eq_finite_diff_on_integral_mconvex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:10:11.945738+00:00
-- url     : https://prove2.me/theorems/deff5453-d6cf-41f2-ac3e-19d7285a885e
-- title:
--   Proposition 6.62 -- dir_deriv_eq_finite_diff_on_integral_mconvex
-- statement:
--   **Proposition 6.62** (p.167). For $f\in M[\mathbb Z|\mathbb R\to\mathbb R]$ and $x\in\operatorname{dom}_{\mathbb R} f\cap\mathbb Z^V$, we have $f'(x;-\chi_u+\chi_v) = f(x-\chi_u+\chi_v)-f(x)$ for $u,v\in V$.
--
--   This shows the two halves of Theorem 6.61 (formalized in mission `24-ch06d-mconvexfunctions`) are consistent with each other: the real-variable directional derivative and the integer-variable finite difference agree exactly at the integer points where both are defined.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.167, Proposition 6.62.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.167, Proposition 6.62

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DirDeriv
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MConvexIntegralR

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.62 (p.167). Consistency of the directional derivative with the finite
difference on `M[Z|R→R]` at an integer point. -/
theorem dir_deriv_eq_finite_diff_on_integral_mconvex (f : (V → ℝ) → WithTop ℝ)
    (hf : MConvexIntegralR f) (x : V → ℝ) (hx : x ∈ DomR f)
    (hxZ : ∀ v, ∃ k : ℤ, x v = (k : ℝ)) (u v : V) :
    DirDeriv f x (fun w => (CharVec v w - CharVec u w : ℝ)) =
      f (fun w => x w - (CharVec u w : ℝ) + (CharVec v w : ℝ)) - f x := by sorry

end DiscreteConvex.MConvexFunctionsE
