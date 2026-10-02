-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsD_dir_deriv_is_pos_homog_mconvex
-- name    : DiscreteConvex.MConvexFunctionsD.dir_deriv_is_pos_homog_mconvex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:58:00.574406+00:00
-- url     : https://prove2.me/theorems/983ebc44-4f4b-4f3b-baeb-a22eb3b12240
-- title:
--   Proposition 6.60 -- dir_deriv_is_pos_homog_mconvex
-- statement:
--   **Proposition 6.60** (p.166). For $f\in M[\mathbb R\to\mathbb R]$ and $x\in\operatorname{dom}_{\mathbb R} f$, the directional derivative $f'(x;\cdot)$ belongs to $0M[\mathbb R\to\mathbb R]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.166, Proposition 6.60.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.166, Proposition 6.60

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DirDeriv
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMR

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.60 (p.185). -/
theorem dir_deriv_is_pos_homog_mconvex (f : (V → ℝ) → WithTop ℝ) (hf : MExchangeAxiomR f)
    (x : V → ℝ) (hx : x ∈ DomR f) : ZeroMR (DirDeriv f x) := by sorry

end DiscreteConvex.MConvexFunctionsD
