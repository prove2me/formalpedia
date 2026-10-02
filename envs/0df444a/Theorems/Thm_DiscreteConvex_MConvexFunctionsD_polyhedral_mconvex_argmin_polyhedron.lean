-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsD_polyhedral_mconvex_argmin_polyhedron
-- name    : DiscreteConvex.MConvexFunctionsD.polyhedral_mconvex_argmin_polyhedron
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:56:08.416733+00:00
-- url     : https://prove2.me/theorems/96a781f3-bfcc-45b0-8d09-cde8f19ab837
-- title:
--   Proposition 6.53 -- polyhedral_mconvex_argmin_polyhedron
-- statement:
--   **Proposition 6.53** (p.163). Let $f\in M[\mathbb R\to\mathbb R]$ be polyhedral M-convex. For any $p\in\mathbb R^V$, $\arg\min f[-p]$ is an M-convex polyhedron if it is not empty.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Proposition 6.53.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Proposition 6.53

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ArgMinOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MConvexPolyhedronR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_LinearWeightR

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.53 (p.182): the minimizer set of a polyhedral M-convex function lies in the
class `M⁰[R]`, which is **not** the integral class. `MConvexPolyhedron` is the convex hull of an
integer M-convex set, and the minimizer set of the indicator of the segment from `(0,0)` to
`(1/2,-1/2)` at `p = 0` is that segment, the hull of no integer set. -/
theorem polyhedral_mconvex_argmin_polyhedron (f : (V → ℝ) → WithTop ℝ)
    (hpoly : IsPolyhedralConvex f) (hf : MExchangeAxiomR f)
    (p : V → ℝ) (hne : (ArgMinOn (LinearWeightR f p)).Nonempty) :
    MConvexPolyhedronR (ArgMinOn (LinearWeightR f p)) := by sorry

end DiscreteConvex.MConvexFunctionsD
