-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_pos_homog_iff_argmin_l0
-- name    : DiscreteConvex.LConvexFunctionsD.pos_homog_iff_argmin_l0
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:05:35.075994+00:00
-- url     : https://prove2.me/theorems/a04c532f-5cd9-4a8d-944f-a3e82c7ca873
-- title:
--   Proposition 7.41 -- pos_homog_iff_argmin_l0
-- statement:
--   **Proposition 7.41** (p.195). For a positively homogeneous polyhedral convex function $g:\mathbb R^V\to\mathbb R\cup\{+\infty\}$ with $\operatorname{dom}_{\mathbb R} g\ne\emptyset$: $g\in 0L[\mathbb R\to\mathbb R]$ iff $\arg\min g[-x]\in L_0[\mathbb R]$ for every $x\in\mathbb R^V$ with $\arg\min g[-x]$ nonempty.
--
--   **Formalization Note.** "$\inf g[-x]>-\infty$" is replaced by the equivalent `(ArgMinR ...).Nonempty` hypothesis, matching mission `25-ch06e-mconvexfunctions`'s identical substitution.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.195, Proposition 7.41.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.195, Proposition 7.41

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_PosHomogeneous
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ArgMinR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexPolyhedron

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.41 (p.195). A positively homogeneous polyhedral convex function is `0L[R→R]`
iff its weighted minimizer sets are always L-convex polyhedra. -/
theorem pos_homog_iff_argmin_l0 (g : (V → ℝ) → WithTop ℝ) (hpos : PosHomogeneous g)
    (hdom : (DomR g).Nonempty) :
    ZeroLR g ↔ ∀ x : V → ℝ, (ArgMinR (LinearWeightR g (fun v => - x v))).Nonempty →
      LConvexPolyhedron (ArgMinR (LinearWeightR g (fun v => - x v))) := by sorry

end DiscreteConvex.LConvexFunctionsD
