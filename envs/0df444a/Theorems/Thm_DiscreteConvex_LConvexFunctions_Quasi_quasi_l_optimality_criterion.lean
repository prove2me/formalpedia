-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctions_Quasi_quasi_l_optimality_criterion
-- name    : DiscreteConvex.LConvexFunctions.Quasi.quasi_l_optimality_criterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:17:43.215448+00:00
-- url     : https://prove2.me/theorems/bf07e266-f58b-4b1e-b8b9-6d0f47a10a0b
-- title:
--   Theorem 7.53 -- the quasi L-optimality criterion
-- statement:
--   **Theorem 7.53** (p.201). Assume $g : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ satisfies $g(p)=g(p+\mathbf 1)$ for all $p$. (1) For $g$ satisfying (QSBw) and $p \in \operatorname{dom} g$: $p$ is the unique minimizer up to translation by $\mathbf 1$ ($g(p) < g(q)$ for every $q$ with $q-p$ not a multiple of $\mathbf 1$) if and only if $g(p) < g(p+\chi_X)$ for every proper nonempty $X \subsetneq V$. (2) For $g$ satisfying (SSQSBw) and $p \in \operatorname{dom} g$, global optimality is equivalent to $g(p) \le g(p+\chi_X)$ for all $X \subseteq V$. The direct analogue of chunk 08's Theorem 7.14 for the quasi-submodularity classes.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.201, Theorem 7.53.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.201, Theorem 7.53

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctions_IndicatorVec
import Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_QSBw
import Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_SSQSBw

open DiscreteConvex.LConvexFunctions

namespace DiscreteConvex.LConvexFunctions.Quasi

/-- Theorem 7.53, the quasi L-optimality criterion (Murota, *Discrete Convex Analysis*, SIAM
2003, p.201). Assume `g : Zⱽ → R ∪ {+∞}` satisfies `g(p) = g(p+1)` for all `p`. (1) For `g`
satisfying (QSBw) and `p ∈ dom g`: `g(p) < g(q)` for every `q` with `q - p` not a multiple of
`1` iff `g(p) < g(p + χ_X)` for every `X ⊆ V` with `X ∉ {∅, V}`. (2) For `g` satisfying
(SSQSBw) and `p ∈ dom g`: `g(p) ≤ g(q)` for all `q` iff `g(p) ≤ g(p + χ_X)` for all `X ⊆ V`. -/
theorem quasi_l_optimality_criterion {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ g : (V → ℤ) → WithTop ℝ, (∀ p : V → ℤ, g (p + 1) = g p) → QSBw g → ∀ p ∈ DomZ g,
      (∀ q : V → ℤ, (¬ ∃ k : ℤ, q = fun v => p v + k) → g p < g q) ↔
        (∀ X : Finset V, X ≠ ∅ → X ≠ Finset.univ →
          g p < g (fun v => p v + IndicatorVec X v))) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, (∀ p : V → ℤ, g (p + 1) = g p) → SSQSBw g → ∀ p ∈ DomZ g,
      (∀ q, g p ≤ g q) ↔ (∀ X : Finset V, g p ≤ g (fun v => p v + IndicatorVec X v))) := by sorry

end DiscreteConvex.LConvexFunctions.Quasi
