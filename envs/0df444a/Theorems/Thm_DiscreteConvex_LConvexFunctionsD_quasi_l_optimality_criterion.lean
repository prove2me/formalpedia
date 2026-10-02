-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_quasi_l_optimality_criterion
-- name    : DiscreteConvex.LConvexFunctionsD.quasi_l_optimality_criterion
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:04:16.81357+00:00
-- url     : https://prove2.me/theorems/a56b2ffd-cc90-42a9-b48c-effb3a034459
-- title:
--   Theorem 7.53 -- quasi_l_optimality_criterion
-- statement:
--   **Theorem 7.53** (Quasi L-optimality criterion; p.201). Assume $g:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ satisfies $g(p)=g(p+\mathbf 1)$. (1) For $g$ satisfying (QSBw) and $p\in\operatorname{dom} g$: $g(p)<g(q)$ for all $q$ with $q-p$ not a multiple of $\mathbf 1$ iff $g(p)<g(p+\chi_X)$ for all $X\notin\{\emptyset,V\}$. (2) For $g$ satisfying (SSQSBw) and $p\in\operatorname{dom} g$: $g(p)\le g(q)$ for all $q$ iff $g(p)\le g(p+\chi_X)$ for all $X\subseteq V$.
--
--   **Not in this chunk's own `BRIEF.md` table** — found by direct reading.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.201, Theorem 7.53.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.201, Theorem 7.53

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IndicatorVec
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QSBw
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SSQSBw
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsMultipleOfOne

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.53 (Quasi L-optimality criterion; p.201). Global optimality of a quasi
submodular, 1-periodic function is characterized by local non-improvement. -/
theorem quasi_l_optimality_criterion (g : (V → ℤ) → WithTop ℝ) (hper : ∀ p : V → ℤ, g (p + 1) = g p) :
    (QSBw g → ∀ p ∈ DomZ g,
      ((∀ q : V → ℤ, ¬ IsMultipleOfOne p q → g p < g q) ↔
        (∀ X : Finset V, X ≠ ∅ → X ≠ Finset.univ →
          g p < g (fun v => p v + IndicatorVec X v)))) ∧
    (SSQSBw g → ∀ p ∈ DomZ g,
      ((∀ q : V → ℤ, g p ≤ g q) ↔
        (∀ X : Finset V, g p ≤ g (fun v => p v + IndicatorVec X v)))) := by sorry

end DiscreteConvex.LConvexFunctionsD
