-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_quasi_m_proximity_theorem
-- name    : DiscreteConvex.MConvexFunctionsE.quasi_m_proximity_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:11:26.766063+00:00
-- url     : https://prove2.me/theorems/68ee12e4-9fd5-4632-95a2-18d9ca5c974f
-- title:
--   Theorem 6.78 -- quasi_m_proximity_theorem
-- statement:
--   **Theorem 6.78** (Quasi M-proximity theorem; p.174-175). Let $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ satisfy (SSQM$\ne$), $n=|V|$, $\alpha\in\mathbb Z_{++}$. If $x_\alpha\in\operatorname{dom} f$ satisfies $f(x_\alpha)\le f(x_\alpha+\alpha(\chi_v-\chi_u))$ for all $u,v$, then $\arg\min f\ne\emptyset$ and some $x^*\in\arg\min f$ has $\|x_\alpha-x^*\|_\infty\le(n-1)(\alpha-1)$ — part (1) of Theorem 6.37 (already formalized as `m_proximity_theorem` in mission `06-mconvex-functions-i`) under this strictly weaker hypothesis. The book's own statement covers only this part (1); part (2)'s M$^\natural$-convex case is not part of Theorem 6.78.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.174-175, Theorem 6.78.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.174-175, Theorem 6.78

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_ArgMinOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMNe

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.78 (p.174-175), the quasi M-proximity theorem: Theorem 6.37 (1) holds under the
weaker (SSQM≠) hypothesis. -/
theorem quasi_m_proximity_theorem (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNe f)
    (alpha : ℤ) (halpha : 0 < alpha) (xalpha : V → ℤ) (hxalpha : xalpha ∈ DomZ f)
    (hcond : ∀ u v : V,
      f xalpha ≤ f (fun w => xalpha w + alpha * (CharVec v w - CharVec u w))) :
    (ArgMinOn f).Nonempty ∧
      ∃ x ∈ ArgMinOn f, ∀ v : V, |xalpha v - x v| ≤ ((Fintype.card V : ℤ) - 1) * (alpha - 1) := by sorry

end DiscreteConvex.MConvexFunctionsE
