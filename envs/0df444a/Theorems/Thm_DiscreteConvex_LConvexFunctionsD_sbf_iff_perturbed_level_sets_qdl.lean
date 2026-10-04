-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_sbf_iff_perturbed_level_sets_qdl
-- name    : DiscreteConvex.LConvexFunctionsD.sbf_iff_perturbed_level_sets_qdl
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T01:02:53.254997+00:00
-- url     : https://prove2.me/theorems/6a9912a2-9226-4df0-8c62-9225fe364293
-- title:
--   Theorem 7.52 -- sbf_iff_perturbed_level_sets_qdl
-- statement:
--   **Theorem 7.52** (p.200-201). A function $g:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ satisfies (SBF[Z]) iff the level set $L(g[x],\alpha)$ satisfies (QDL) for all $x\in\mathbb R^V$ and $\alpha\in\mathbb R$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.200-201, Theorem 7.52.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.200-201, Theorem 7.52

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QDL
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LevelSet
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightPlus

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.52 (p.200-201). (SBF[Z]) is equivalent to (QDL) of every level set of every linear
perturbation of `g`. -/
theorem sbf_iff_perturbed_level_sets_qdl (g : (V → ℤ) → WithTop ℝ) :
    SBF g ↔ ∀ x : V → ℝ, ∀ alpha : ℝ, QDL (LevelSet (LinearWeightPlus g x) alpha) := by sorry

end DiscreteConvex.LConvexFunctionsD
