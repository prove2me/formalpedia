-- Prove2me | Theorems.Thm_ErrBoundQG_Structured_quadratic_growth
-- name    : ErrBoundQG.Structured.quadratic_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:56.275876+00:00
-- url     : https://prove2.me/theorems/9e4f7ad4-df61-4e35-bfbb-4d6d5f04af5f
-- title:
--   Theorem 4.2 proof, p. 11 — quadratic growth on every sublevel set
-- statement:
--   In the setting of Theorem 4.2, assume the primal minimizer set $S$ is nonempty and bounded, dual nondegeneracy and strict complementarity hold, and the two components are firmly convex relative to the indicated dual vectors. For every $\nu>0$, some $\mu>0$ satisfies
--
--   $$\varphi(x)\ge\varphi^*+\mu\operatorname{dist}^2(x,S)\qquad\text{whenever }\varphi(x)\le\varphi^*+\nu.$$
--
--   This is the quadratic-growth conclusion in the proof of Theorem 4.2, before applying the proximal-gradient equivalence of §3.
--
--   **Formalization Note.** The paper's coefficient is $\min\{\alpha,c\}/(4\kappa^2)$ for constants from (4.4)–(4.5); the statement existentially quantifies this positive coefficient.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 11, proof of Theorem 4.2 after (4.5)

import Mathlib
import Definitions.Def_ErrBoundQG_Structured_Setting

namespace ErrBoundQG.Structured

/-- The quadratic-growth conclusion at the end of Theorem 4.2's proof, p. 11. -/
theorem quadratic_growth {m n : ℕ}
    (f : E m → ℝ) (hf : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ Set.univ f)
    (g : E n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g) (A : E n →L[ℝ] E m)
    (S : Set (E n)) (hS : S = {x | ∀ z, primalObj f g A x ≤ primalObj f g A z})
    (hSne : S.Nonempty) (hSbd : Bornology.IsBounded S) (ybar : E m)
    (hybar : ∀ y, dualObj f g A ybar ≤ dualObj f g A y)
    (hnd : DualNondegenerate f g A)
    (hsc : DualStrictComplementarity f g A ybar)
    (hffirm : FirmlyConvexRel (fun z => (f z : EReal)) ybar)
    (hgfirm : FirmlyConvexRel g (-(ContinuousLinearMap.adjoint A ybar)))
    (φstar : ℝ) (hstar : ∀ x ∈ S, primalObj f g A x = (φstar : EReal)) :
    ∀ ν : ℝ, 0 < ν → ∃ μ : ℝ, 0 < μ ∧
      ∀ x : E n, primalObj f g A x ≤ ((φstar + ν : ℝ) : EReal) →
        ((φstar + μ * Metric.infDist x S ^ 2 : ℝ) : EReal) ≤ primalObj f g A x := by sorry

end ErrBoundQG.Structured
