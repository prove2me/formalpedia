-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctions_Quasi_quasi_m_optimality_criterion
-- name    : DiscreteConvex.MConvexFunctions.Quasi.quasi_m_optimality_criterion
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:03:33.922292+00:00
-- url     : https://prove2.me/theorems/55974ae7-f440-45bd-8081-642bfdbae700
-- title:
--   Theorem 6.76 -- the quasi M-optimality criterion
-- statement:
--   **Theorem 6.76** (p.173). (1) For $f$ satisfying (QMw) and $x \in \operatorname{dom} f$, $x$ is the *unique* minimizer ($f(x) < f(y)$ for all $y \ne x$) if and only if $f(x) < f(x-\chi_u+\chi_v)$ for all $u \ne v$ in $V$. (2) For $f$ satisfying (SSQM$_{\ne,w}$) and $x \in \operatorname{dom} f$, $x$ globally minimizes $f$ if and only if $f(x) \le f(x-\chi_u+\chi_v)$ for all $u,v \in V$. This is the direct analogue of chunk 06's Theorem 6.26 for the strictly larger quasi-convexity classes.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.173, Theorem 6.76.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.173, Theorem 6.76

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_SSQMNeqW

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.MConvexFunctions.Quasi

/-- Theorem 6.76, the quasi M-optimality criterion (Murota, *Discrete Convex Analysis*, SIAM
2003, p.173). (1) For `f` satisfying (QMw) and `x ∈ dom f`, `f(x) < f(y)` for all `y ≠ x` iff
`f(x) < f(x - χ_u + χ_v)` for all `u, v ∈ V` with `u ≠ v`. (2) For `f` satisfying (SSQM≠_w) and
`x ∈ dom f`, `f(x) ≤ f(y)` for all `y` iff `f(x) ≤ f(x - χ_u + χ_v)` for all `u, v ∈ V`. -/
theorem quasi_m_optimality_criterion {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ f : (V → ℤ) → WithTop ℝ, QMw f → ∀ x ∈ DomZ f,
      (∀ y : V → ℤ, y ≠ x → f x < f y) ↔
        (∀ u v : V, u ≠ v → f x < f (fun w => x w - CharVec u w + CharVec v w))) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, SSQMNeqW f → ∀ x ∈ DomZ f,
      (∀ y, f x ≤ f y) ↔
        (∀ u v : V, f x ≤ f (fun w => x w - CharVec u w + CharVec v w))) := by sorry

end DiscreteConvex.MConvexFunctions.Quasi
