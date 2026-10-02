-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDuality_m_convex_intersection_theorem
-- name    : DiscreteConvex.ConjugacyDuality.m_convex_intersection_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:10:22.404992+00:00
-- url     : https://prove2.me/theorems/946218ae-33e2-4e24-ba4d-95b9f5ee7408
-- title:
--   Theorem 8.17 -- the M-convex intersection theorem
-- statement:
--   **Theorem 8.17** (p.219). For M$^\natural$-convex functions $f_1, f_2$ and a point $x^* \in \operatorname{dom}_{\mathbb Z} f_1 \cap \operatorname{dom}_{\mathbb Z} f_2$, $x^*$ jointly minimizes $f_1+f_2$ if and only if there is a linear functional $p^* \in \mathbb R^V$ separately certifying $x^*$ as a minimizer of the perturbations $f_1[-p^*]$ and $f_2[+p^*]$. This is the function-level generalization of chunk 04's Edmonds's intersection theorem (M-convex *sets*): it shows the same min-max structure governs joint minimization of a pair of M-convex functions, not merely intersection of their domains.
--
--   **Formalization Note.** The two perturbed-optimality conditions are stated additively (moving the linear shift $\langle p^*,\cdot\rangle$ to the other side of each inequality) to avoid subtraction on `WithTop ℝ`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.219, Theorem 8.17.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.219, Theorem 8.17

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNaturalConvex

namespace DiscreteConvex.ConjugacyDuality

/-- Theorem 8.17, the M-convex intersection theorem (Murota, *Discrete Convex Analysis*, SIAM
2003, p.219). For M♮-convex functions `f1, f2` and a point `x* ∈ dom_Z f1 ∩ dom_Z f2`,
`f1(x*) + f2(x*) ≤ f1(x) + f2(x)` for all `x ∈ Zⱽ` if and only if there exists `p* ∈ Rⱽ` such
that `f1[-p*](x*) ≤ f1[-p*](x)` and `f2[+p*](x*) ≤ f2[+p*](x)` for all `x ∈ Zⱽ`, where
`f[q](y) = f(y) - ⟨q,y⟩`; the two perturbed inequalities are stated additively (moving the
linear shift to the other side) to avoid subtraction on `WithTop ℝ`. -/
theorem m_convex_intersection_theorem {V : Type*} [Fintype V] [DecidableEq V]
    (f1 f2 : (V → ℤ) → WithTop ℝ)
    (hf1 : DiscreteConvex.MConvexFunctions.MNaturalConvex f1)
    (hf2 : DiscreteConvex.MConvexFunctions.MNaturalConvex f2)
    (xstar : V → ℤ) (hx1 : xstar ∈ DomZ f1) (hx2 : xstar ∈ DomZ f2) :
    (∀ x : V → ℤ, f1 xstar + f2 xstar ≤ f1 x + f2 x) ↔
      (∃ p : V → ℝ,
        (∀ x : V → ℤ,
          f1 xstar + ((∑ v, (xstar v : ℝ) * p v : ℝ) : WithTop ℝ) ≤
            f1 x + ((∑ v, (x v : ℝ) * p v : ℝ) : WithTop ℝ)) ∧
        (∀ x : V → ℤ,
          f2 xstar + ((∑ v, (x v : ℝ) * p v : ℝ) : WithTop ℝ) ≤
            f2 x + ((∑ v, (xstar v : ℝ) * p v : ℝ) : WithTop ℝ))) := by sorry

end DiscreteConvex.ConjugacyDuality
