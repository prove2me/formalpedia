-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_mexchange_iff_perturbed_level_sets_qexcw
-- name    : DiscreteConvex.MConvexFunctionsE.mexchange_iff_perturbed_level_sets_qexcw
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:08:53.591973+00:00
-- url     : https://prove2.me/theorems/8cc8e953-11f8-4502-9d47-51b48b444061
-- title:
--   Theorem 6.74 -- mexchange_iff_perturbed_level_sets_qexcw
-- statement:
--   **Theorem 6.74** (p.172). A function $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ satisfies (M-EXC[Z]) if and only if the level set $L(f[p],\alpha)$ satisfies (Q-EXCw) for all $p\in\mathbb R^V$ and $\alpha\in\mathbb R$.
--
--   An M-convex function is characterized entirely by the quasi M-convexity of the level sets of its every linear perturbation — used directly by the goal, Theorem 6.68.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.172, Theorem 6.74.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.172, Theorem 6.74

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QEXCw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_LevelSet
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_LinearWeight

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.74 (p.172). (M-EXC[Z]) is equivalent to (Q-EXCw) of every level set of every
linear perturbation of `f`. -/
theorem mexchange_iff_perturbed_level_sets_qexcw (f : (V → ℤ) → WithTop ℝ) :
    MExchangeAxiom f ↔ ∀ p : V → ℝ, ∀ alpha : ℝ, QEXCw (LevelSet (LinearWeight f p) alpha) := by sorry

end DiscreteConvex.MConvexFunctionsE
