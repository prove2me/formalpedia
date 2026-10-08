-- Prove2me | Theorems.Thm_ExpConeIPM_Corrector_homogeneity_identities
-- name    : ExpConeIPM.Corrector.homogeneity_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:05:40.187568+00:00
-- url     : https://prove2.me/theorems/4460500b-4afe-4d41-9af7-f8fd8e863976
-- title:
--   §2 — consequences of logarithmic homogeneity: $F'(\tau x)=F'(x)/\tau$, $F''(\tau x)=F''(x)/\tau^2$, $F''(x)x=-F'(x)$, $F'''(x)x=-2F''(x)$, $\langle F'(x),x\rangle=-\vartheta$
-- statement:
--   Let $K\subseteq\mathbb R^N$ be a proper cone (pointed, closed, convex, with nonempty interior) and let $F$ be a $\vartheta$-logarithmically homogeneous self-concordant barrier for $K$, so that in particular $F(\tau x)=F(x)-\vartheta\log\tau$ for $x\in\operatorname{int}K$ and $\tau>0$. Then for every $x\in\operatorname{int}K$ and every $\tau>0$,
--   $$F'(\tau x)=\frac1\tau F'(x),\qquad F''(\tau x)=\frac1{\tau^2}F''(x),\qquad F''(x)x=-F'(x),\qquad F'''(x)[x]=-2F''(x),\qquad \langle F'(x),x\rangle=-\vartheta .$$
--   Here $F'$ is the gradient, $F''$ the Hessian, and $F'''(x)[x]$ is the third derivative contracted once with $x$, a linear map.
--
--   These identities are the algebraic engine of the paper's analysis: $F'''(x)[x]=-2F''(x)$ is what makes the corrector (16) orthogonal to the complementarity gap (Lemma 3), and $\langle F'(x),x\rangle=-\vartheta$ turns the centering term $\gamma\mu\tilde v$ into $\gamma\langle x,s\rangle$ (Lemma 4).
--
--   **Formalization Note** $F'$ is `gradient F`, $F''$ is the published `hess F` (the derivative of the gradient), and $F'''(x)[x]$ is `fderiv ℝ (hess F) x x`. The barrier is the published `IsLogHomBarrier`, which contains the paper's two conditions (self-concordance with $F\in C^3$, logarithmic homogeneity) plus three standard ones the paper uses implicitly (boundary blow-up, the $\vartheta$-inequality, positive definite Hessian).
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 345, §2 (consequences of the homogeneity property)

import Mathlib
import Definitions.Def_SelfScaledIPM_ShortStep_Setting

open scoped InnerProductSpace

namespace ExpConeIPM.Corrector

/-- **§2 homogeneity identities** (Dahl–Andersen, Math. Program. 194 (2022), p. 345). Let `K ⊆ ℝᴺ`
be a proper cone and `F` a `ϑ`-logarithmically homogeneous self-concordant barrier for `K`. Then for
every `x ∈ int K` and `τ > 0`:
`F'(τx) = (1/τ) F'(x)`, `F''(τx) = (1/τ²) F''(x)`, `F''(x)x = −F'(x)`, `F'''(x)[x] = −2F''(x)`,
`⟨F'(x), x⟩ = −ϑ`.
`F' = gradient F`, `F'' = hess F`, and `F'''(x)[x] = fderiv ℝ (hess F) x x`, a linear map. -/
theorem homogeneity_identities {N : ℕ} (K : Set (EuclideanSpace ℝ (Fin N)))
    (F : EuclideanSpace ℝ (Fin N) → ℝ) (ϑ : ℝ)
    (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (hF : SelfScaledIPM.ShortStep.IsLogHomBarrier K F ϑ)
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ∈ interior K) (τ : ℝ) (hτ : 0 < τ) :
    gradient F (τ • x) = (1 / τ) • gradient F x ∧
      SelfScaledIPM.ShortStep.hess F (τ • x) = (1 / τ ^ 2) • SelfScaledIPM.ShortStep.hess F x ∧
      SelfScaledIPM.ShortStep.hess F x x = -gradient F x ∧
      fderiv ℝ (SelfScaledIPM.ShortStep.hess F) x x = (-2 : ℝ) • SelfScaledIPM.ShortStep.hess F x ∧
      ⟪gradient F x, x⟫_ℝ = -ϑ := by sorry

end ExpConeIPM.Corrector
