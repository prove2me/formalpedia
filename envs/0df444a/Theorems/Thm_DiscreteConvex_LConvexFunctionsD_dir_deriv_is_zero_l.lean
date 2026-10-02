-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_dir_deriv_is_zero_l
-- name    : DiscreteConvex.LConvexFunctionsD.dir_deriv_is_zero_l
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:05:32.788286+00:00
-- url     : https://prove2.me/theorems/0d5d7e9f-ec0c-487f-b4ce-1500b898a8af
-- title:
--   Proposition 7.42 -- dir_deriv_is_zero_l
-- statement:
--   **Proposition 7.42** (p.196). If $g\in L[\mathbb R\to\mathbb R]$ and $p\in\operatorname{dom}_{\mathbb R} g$, then $g'(p;\cdot)\in 0L[\mathbb R\to\mathbb R]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.196, Proposition 7.42.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.196, Proposition 7.42

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DirDeriv

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.42 (p.196). The directional derivative of a polyhedral L-convex function is
positively homogeneous L-convex. -/
theorem dir_deriv_is_zero_l (g : (V → ℝ) → WithTop ℝ) (hg : SBFR g ∧ TRFR g) (p : V → ℝ)
    (hp : p ∈ DomR g) : ZeroLR (fun d => DirDeriv g p d) := by sorry

end DiscreteConvex.LConvexFunctionsD
