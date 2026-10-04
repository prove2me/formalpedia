-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctions_m_proximity_theorem
-- name    : DiscreteConvex.MConvexFunctions.m_proximity_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:59:39.821658+00:00
-- url     : https://prove2.me/theorems/667759a7-dc41-4fc0-9470-37976e23b287
-- title:
--   Theorem 6.37 -- the M-proximity theorem
-- statement:
--   **Theorem 6.37** (p.156). Assume $\alpha \in \mathbb Z_{++}$ and $n = |V|$. (1) Let $f$ be an M-convex function. If $x_\alpha \in \operatorname{dom} f$ satisfies $f(x_\alpha) \le f(x_\alpha + \alpha(\chi_v - \chi_u))$ for all $u,v \in V$, then $\arg\min f \ne \emptyset$ and there is $x^* \in \arg\min f$ with $\|x_\alpha - x^*\|_\infty \le (n-1)(\alpha-1)$. (2) Let $f$ be M$^\natural$-convex. If $x_\alpha$ satisfies the same inequality for all $u,v \in V \cup \{0\}$ (with $\chi_0 = 0$), then $\arg\min f \ne \emptyset$ and there is $x^* \in \arg\min f$ with $\|x_\alpha - x^*\|_\infty \le n(\alpha-1)$.
--
--   A point that looks locally optimal *at scale $\alpha$* (only checked against neighbors $\alpha$ steps away) is provably within an explicit, dimension-and-scale-only distance of a true minimizer — this is what makes the scaling algorithms of chapter 10 correct. The two parts have genuinely different bounds ($(n-1)(\alpha-1)$ vs. $n(\alpha-1)$) for genuinely different hypothesis classes (M-convex vs. M$^\natural$-convex, with a wider index range $V \cup \{0\}$ in the second case); neither bound is a special case of the other, and both are kept exact.
--
--   **Formalization Note.** $\|z\|_\infty \le c$ is stated pointwise ($\forall v, |z(v)| \le c$), equivalent to but avoiding a separate norm definition.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.156, Theorem 6.37.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.156, Theorem 6.37

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVecOpt

namespace DiscreteConvex.MConvexFunctions

/-- Theorem 6.37, the M-proximity theorem (Murota, *Discrete Convex Analysis*, SIAM 2003,
p.156). Assume `α ∈ Z++` and `n = |V|`. (1) Let `f` be M-convex. If `xα ∈ dom f` satisfies
`f(xα) ≤ f(xα + α(χ_v - χ_u))` for all `u, v ∈ V`, then `arg min f ≠ ∅` and there is
`x* ∈ arg min f` with `‖xα - x*‖∞ ≤ (n-1)(α-1)`. (2) Let `f` be M♮-convex. If `xα ∈ dom f`
satisfies `f(xα) ≤ f(xα + α(χ_v - χ_u))` for all `u, v ∈ V ∪ {0}` (with `χ₀ = 0`), then
`arg min f ≠ ∅` and there is `x* ∈ arg min f` with `‖xα - x*‖∞ ≤ n(α-1)`. -/
theorem m_proximity_theorem {V : Type*} [Fintype V] [DecidableEq V] (α : ℤ) (hα : 0 < α) :
    (∀ f : (V → ℤ) → WithTop ℝ, MExchangeAxiom f → ∀ xα ∈ DomZ f,
        (∀ u v : V, f xα ≤ f (fun w => xα w + α * (CharVec v w - CharVec u w))) →
        (ArgMin f).Nonempty ∧
          ∃ x ∈ ArgMin f, ∀ v : V, |xα v - x v| ≤ ((Fintype.card V : ℤ) - 1) * (α - 1)) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, MNaturalConvex f → ∀ xα ∈ DomZ f,
        (∀ u v : Option V,
            f xα ≤ f (fun w => xα w + α * (CharVecOpt v w - CharVecOpt u w))) →
        (ArgMin f).Nonempty ∧
          ∃ x ∈ ArgMin f, ∀ v : V, |xα v - x v| ≤ (Fintype.card V : ℤ) * (α - 1)) := by sorry

end DiscreteConvex.MConvexFunctions
