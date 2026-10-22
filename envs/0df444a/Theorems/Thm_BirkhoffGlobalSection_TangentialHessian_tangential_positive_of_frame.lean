-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_tangential_positive_of_frame
-- name    : BirkhoffGlobalSection.TangentialHessian.tangential_positive_of_frame
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-26T17:40:11.009987+00:00
-- url     : https://prove2.me/theorems/3b86a386-85f6-4e3d-a131-1b360578b7b4
-- title:
--   Tangential Hessian in the quaternionic frame $I\nabla F, J\nabla F, K\nabla F$
-- statement:
--   Let $F:\mathbb R^4\to\mathbb R$ be $C^2$ at $s$, with nonzero gradient $g=\nabla F(s)$. Let $I,J,K$ be the quaternionic matrices of Section 2.3 and $v_1=Ig$, $v_2=Jg$, $v_3=Kg$. Suppose that the $3\times3$ tangential Hessian in this frame is positive definite:
--
--   $$
--   \sum_{i,j=1}^3 a_ia_j\,D^2F(s)(v_i,v_j)>0\qquad\text{for all }a\in\mathbb R^3\setminus\{0\}.
--   $$
--
--   Then for every nonzero $v\in\mathbb R^4$ with $DF(s)[v]=0$,
--
--   $$
--   D\big(x\mapsto DF(x)[v]\big)(s)[v]\;>\;0 .
--   $$
--
--   This is the linear-algebra step behind the use of $\mathrm{THess}$ in Joung–van Koert. The vectors $Ig,Jg,Kg$ are pairwise orthogonal, orthogonal to $g$, and all of length $\lvert g\rvert$, so they span $\ker DF(s)$. Positive definiteness of the $3\times3$ matrix is therefore equivalent to the tangential-Hessian condition at $s$.
--
--   **Formalization Note.** `grad F s` is the vector of partial derivatives, and `frame g` is $(Ig,Jg,Kg)$. The conclusion is stated with iterated Fréchet derivatives, exactly as in the platform predicate `HasPositiveTangentialHessianOn`.
-- source:
--   Joung–van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Section 2.3 (definition of THess via the frame I∇K, J∇K, K∇K).

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian

namespace BirkhoffGlobalSection.TangentialHessian

/-- If the gradient is nonzero and the `3 × 3` tangential Hessian in the quaternionic
frame `I∇F, J∇F, K∇F` is positive definite, then `D²F(s)(v,v) > 0` for every nonzero
`v` with `DF(s) v = 0`. -/
theorem tangential_positive_of_frame (F : Phase → ℝ) (s : Phase)
    (hF : ContDiffAt ℝ 2 F s) (hg : grad F s ≠ 0)
    (hpos : ∀ a : Fin 3 → ℝ, a ≠ 0 →
      0 < ∑ i : Fin 3, ∑ j : Fin 3, a i * a j *
        fderiv ℝ (fderiv ℝ F) s (frame (grad F s) i) (frame (grad F s) j))
    (v : Phase) (hv : v ≠ 0) (hker : fderiv ℝ F s v = 0) :
    0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v := by sorry

end BirkhoffGlobalSection.TangentialHessian
