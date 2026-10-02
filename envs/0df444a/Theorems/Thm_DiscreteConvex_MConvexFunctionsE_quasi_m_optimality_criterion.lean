-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_quasi_m_optimality_criterion
-- name    : DiscreteConvex.MConvexFunctionsE.quasi_m_optimality_criterion
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:11:11.140902+00:00
-- url     : https://prove2.me/theorems/e3b3f75a-afd5-4404-ba8c-fa0a325f37fd
-- title:
--   Theorem 6.76 -- quasi_m_optimality_criterion
-- statement:
--   **Theorem 6.76** (Quasi M-optimality criterion; p.173-174). (1) For $f$ satisfying (QMw) and $x\in\operatorname{dom} f$: $f(x)<f(y)$ for all $y\ne x$ iff $\Delta f(x;v,u)>0$ for all $u\ne v$. (2) For $f$ satisfying (SSQM$\ne_w$) and $x\in\operatorname{dom} f$: $f(x)\le f(y)$ for all $y$ iff $\Delta f(x;v,u)\ge 0$ for all $u,v$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.173-174, Theorem 6.76.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.173-174, Theorem 6.76

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DeltaF
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMNeW

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.76 (p.173-174). The quasi M-optimality criterion. -/
theorem quasi_m_optimality_criterion (f : (V → ℤ) → WithTop ℝ) :
    (QMw f → ∀ x ∈ DomZ f,
        ((∀ y : V → ℤ, y ≠ x → f x < f y) ↔ ∀ u v : V, u ≠ v → DeltaF f x v u > 0)) ∧
    (SSQMNeW f → ∀ x ∈ DomZ f,
        ((∀ y : V → ℤ, f x ≤ f y) ↔ ∀ u v : V, DeltaF f x v u ≥ 0)) := by sorry

end DiscreteConvex.MConvexFunctionsE
