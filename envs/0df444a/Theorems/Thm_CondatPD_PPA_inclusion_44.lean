-- Prove2me | Theorems.Thm_CondatPD_PPA_inclusion_44
-- name    : CondatPD.PPA.inclusion_44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:35:26.145289+00:00
-- url     : https://prove2.me/theorems/ab1f4d7e-dd14-462c-8340-e0aa4f54af85
-- title:
--   Inclusion (44), p. 13 — error-free Algorithm 3.2 step satisfies −B(zₙ) ∈ A(z̃ₙ₊₁) + P′(z̃ₙ₊₁ − zₙ)
-- statement:
--   Let $\mathcal X,\mathcal Y$, $L$, $F$ (convex, differentiable, $\beta$-Lipschitz gradient, (2)), $G\in\Gamma_0(\mathcal X)$, $H\in\Gamma_0(\mathcal Y)$, $\tau>0$, $\sigma>0$ be as in (22). Let $z_n=(x_n,y_n)$ and let $\tilde z_{n+1}=(\tilde x_{n+1},\tilde y_{n+1})$ be computed by Algorithm 3.2 with zero error terms:
--   $$\tilde y_{n+1}=\mathrm{prox}_{\sigma H^*}(y_n+\sigma Lx_n),\qquad \tilde x_{n+1}=\mathrm{prox}_{\tau G}\big(x_n-\tau\nabla F(x_n)-\tau L^*(2\tilde y_{n+1}-y_n)\big).$$
--   Then
--   $$-\begin{pmatrix}\nabla F(x_n)\\0\end{pmatrix}\in A(\tilde z_{n+1})+P'(\tilde z_{n+1}-z_n),\qquad P'=\begin{pmatrix}\frac1\tau I&L^*\\L&\frac1\sigma I\end{pmatrix},$$
--   with $A(x,y)=(\partial G(x)+L^*y)\times(-Lx+\partial H^*(y))$. Componentwise, $\tfrac1\sigma(y_n-\tilde y_{n+1})+Lx_n\in\partial H^*(\tilde y_{n+1})$ and $\tfrac1\tau(x_n-\tilde x_{n+1})-\nabla F(x_n)-L^*(2\tilde y_{n+1}-y_n)\in\partial G(\tilde x_{n+1})$.
--
--   Comparing (22) and (44) is how the paper transfers the whole analysis of Algorithm 3.1 to Algorithm 3.2, replacing $P$ by $P'$.
--
--   **Formalization Note** Encoded as for (22): prox maps with the `IsProx` property, $\mathcal Z_I$ as `WithLp 2 (X × Y)`, the standing assumption (2) on $F$ as `IsSmoothTerm β F`, and the inclusion as $-(\nabla F(x_n),0)-P'(\tilde z_{n+1}-z_n)\in A(\tilde z_{n+1})$ with $P'$ written out.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 13, §4, proof of Theorems 3.1, 3.2, 3.3 for Algorithm 3.2, (44)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_CondatPD_PPA_Setting

namespace CondatPD.PPA

theorem inclusion_44 {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → ℝ) (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (β : ℝ) (hF : IsSmoothTerm β F)
    (hG : ThreeOpSplitting.ConvexRates.IsProperClosedConvex G)
    (hH : ThreeOpSplitting.ConvexRates.IsProperClosedConvex H)
    (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (PG : X → X) (PH : Y → Y)
    (hPG : ThreeOpSplitting.ConvexRates.IsProx τ G PG)
    (hPH : ThreeOpSplitting.ConvexRates.IsProx σ (MoreauProx.Characterization.conj H) PH)
    (xn xt : X) (yn yt : Y)
    (hyt : yt = PH (yn + σ • L xn))
    (hxt : xt = PG (xn - τ • gradient F xn
      - τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • yt - yn))) :
    -WithLp.toLp 2 (gradient F xn, (0 : Y))
        - WithLp.toLp 2 (τ⁻¹ • (xt - xn) + ContinuousLinearMap.adjoint L (yt - yn),
            L (xt - xn) + σ⁻¹ • (yt - yn))
      ∈ opA G H L (WithLp.toLp 2 (xt, yt)) := by sorry

end CondatPD.PPA
