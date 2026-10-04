-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsB_univariate_and_pair_lconvexity
-- name    : DiscreteConvex.LConvexFunctionsB.univariate_and_pair_lconvexity
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:25:29.510468+00:00
-- url     : https://prove2.me/theorems/17fb8682-6e02-4060-9c09-44a988d313a6
-- title:
--   Proposition 7.9 -- univariate_and_pair_lconvexity
-- statement:
--   **Proposition 7.9** (p.183). Let $\psi\in C[\mathbb Z\to\mathbb R]$ be univariate discrete convex. (1) $\psi$ is L$^\natural$-convex. (2) The function $g:\mathbb Z^2\to\mathbb R\cup\{+\infty\}$ defined by $g(p)=\psi(p(1)-p(2))$ is L-convex.
--
--   **Formalization Note.** Part (1) is stated with the ground set represented as `Unit` (a single coordinate); part (2) with the ground set `Fin 2`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.183, Proposition 7.9.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.183, Proposition 7.9

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_DiscreteConvexUnivariate

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.9 (p.183). A univariate discrete convex function is L♮-convex; the two-variable
difference function it induces is L-convex. -/
theorem univariate_and_pair_lconvexity (psi : ℤ → WithTop ℝ) (hpsi : DiscreteConvexUnivariate psi) :
    LNaturalConvex (fun p : Unit → ℤ => psi (p ())) ∧
    (SBF (fun p : Fin 2 → ℤ => psi (p 0 - p 1)) ∧ TRF (fun p : Fin 2 → ℤ => psi (p 0 - p 1))) := by sorry

end DiscreteConvex.LConvexFunctionsB
