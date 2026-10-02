-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsC_mconvex_minimizer_cut_scaling
-- name    : DiscreteConvex.MConvexFunctionsC.mconvex_minimizer_cut_scaling
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:30:38.8721+00:00
-- url     : https://prove2.me/theorems/82c69de2-db54-425f-9d3f-13cd9bfa8826
-- title:
--   Theorem 6.39 -- mconvex_minimizer_cut_scaling
-- statement:
--   **Theorem 6.39** (M-minimizer cut with scaling; p.158). Let $f$ be M-convex with $\arg\min f \ne \emptyset$, $\alpha$ a positive integer, $n=|V|$. (1) For $x\in\operatorname{dom} f$, $v\in V$, and $u$ minimizing $f(x+\alpha(\chi_v-\chi_u))$ over shifts at $v$, some minimizer $x^*$ of $f$ has $x^*(u) \le x(u) - \alpha(1-\chi_v(u)) + (n-1)(\alpha-1)$. (2) The symmetric statement for the lower bound at $v$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.158, Theorem 6.39.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.158, Theorem 6.39

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ArgMinOn

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.39 (p.158), M-minimizer cut with scaling. -/
theorem mconvex_minimizer_cut_scaling (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (hne : (ArgMinOn f).Nonempty) (alpha : ℤ) (halpha : 0 < alpha) :
    (∀ x ∈ DomZ f, ∀ v u : V,
        (∀ s : V, f (fun w => x w + alpha * (CharVec v w - CharVec u w)) ≤
          f (fun w => x w + alpha * (CharVec v w - CharVec s w))) →
        ∃ xstar ∈ ArgMinOn f,
          xstar u ≤ x u - alpha * (1 - CharVec v u) + ((Fintype.card V : ℤ) - 1) * (alpha - 1)) ∧
    (∀ x ∈ DomZ f, ∀ u v : V,
        (∀ t : V, f (fun w => x w + alpha * (CharVec v w - CharVec u w)) ≤
          f (fun w => x w + alpha * (CharVec t w - CharVec u w))) →
        ∃ xstar ∈ ArgMinOn f,
          xstar v ≥ x v + alpha * (1 - CharVec u v) - ((Fintype.card V : ℤ) - 1) * (alpha - 1)) := by sorry

end DiscreteConvex.MConvexFunctionsC
