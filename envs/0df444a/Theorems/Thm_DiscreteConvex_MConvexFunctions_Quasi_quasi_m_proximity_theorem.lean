-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctions_Quasi_quasi_m_proximity_theorem
-- name    : DiscreteConvex.MConvexFunctions.Quasi.quasi_m_proximity_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:03:39.117998+00:00
-- url     : https://prove2.me/theorems/ada78970-32f7-428a-a928-55b47fc1ebbd
-- title:
--   Theorem 6.78 -- the quasi M-proximity theorem
-- statement:
--   **Theorem 6.78** (p.174). Let $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ satisfy (SSQM$_{\ne}$), $n = |V|$, and $\alpha \in \mathbb Z_{++}$. If $x_\alpha \in \operatorname{dom} f$ satisfies $f(x_\alpha) \le f(x_\alpha + \alpha(\chi_v-\chi_u))$ for all $u,v \in V$, then $\arg\min f \ne \emptyset$ and there exists $x^* \in \arg\min f$ with $\|x_\alpha - x^*\|_\infty \le (n-1)(\alpha-1)$ — the same conclusion, and the same exact bound, as chunk 06's Theorem 6.37(1) for M-convex functions, but now proved for the strictly larger class of functions satisfying (SSQM$_{\ne}$) rather than the M-convex exchange axiom itself. This is a genuine generalization, not a restatement: (SSQM$_{\ne}$) arises, for instance, from applying any strictly increasing scalar transformation to an M-convex function (Example 6.66), a class of functions the M-convex proximity theorem alone says nothing about.
--
--   **Formalization Note.** $\|z\|_\infty \le c$ is stated pointwise, as in chunk 06's Theorem 6.37.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.174, Theorem 6.78.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.174, Theorem 6.78

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
import Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_SSQMNeq

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.MConvexFunctions.Quasi

/-- Theorem 6.78, the quasi M-proximity theorem (Murota, *Discrete Convex Analysis*, SIAM 2003,
p.174). Let `f : Zⱽ → R ∪ {+∞}` satisfy (SSQM≠), `n = |V|`, and `α ∈ Z++`. If
`xα ∈ dom f` satisfies `f(xα) ≤ f(xα + α(χ_v - χ_u))` for all `u, v ∈ V`, then
`arg min f ≠ ∅` and there exists `x* ∈ arg min f` with `‖xα - x*‖∞ ≤ (n-1)(α-1)` — the same
conclusion as Theorem 6.37(1) (chunk `06-mconvex-functions-i`), but for the strictly larger
class of functions satisfying (SSQM≠) rather than the M-convex exchange axiom. -/
theorem quasi_m_proximity_theorem {V : Type*} [Fintype V] [DecidableEq V] (α : ℤ) (hα : 0 < α)
    (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNeq f) (xα : V → ℤ) (hxα : xα ∈ DomZ f)
    (hloc : ∀ u v : V, f xα ≤ f (fun w => xα w + α * (CharVec v w - CharVec u w))) :
    (ArgMin f).Nonempty ∧
      ∃ x ∈ ArgMin f, ∀ v : V, |xα v - x v| ≤ ((Fintype.card V : ℤ) - 1) * (α - 1) := by sorry

end DiscreteConvex.MConvexFunctions.Quasi
