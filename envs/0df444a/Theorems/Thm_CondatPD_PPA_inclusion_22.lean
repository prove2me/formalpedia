-- Prove2me | Theorems.Thm_CondatPD_PPA_inclusion_22
-- name    : CondatPD.PPA.inclusion_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:35:16.220508+00:00
-- url     : https://prove2.me/theorems/24a7b527-b283-4d5f-82f7-4b0a71866850
-- title:
--   Inclusion (22), p. 10 — error-free Algorithm 3.1 step satisfies −B(zₙ) ∈ A(z̃ₙ₊₁) + P(z̃ₙ₊₁ − zₙ)
-- statement:
--   Let $\mathcal X,\mathcal Y$ be real Hilbert spaces, $L:\mathcal X\to\mathcal Y$ bounded linear, $F:\mathcal X\to\mathbb R$ convex and differentiable with $\beta$-Lipschitz gradient for some $\beta\in[0,+\infty[$ (2), $G\in\Gamma_0(\mathcal X)$, $H\in\Gamma_0(\mathcal Y)$, $\tau>0$, $\sigma>0$. Let $z_n=(x_n,y_n)\in\mathcal X\times\mathcal Y$ and let $\tilde z_{n+1}=(\tilde x_{n+1},\tilde y_{n+1})$ be computed by Algorithm 3.1 in the error-free case $e_{F,n}=e_{G,n}=e_{H,n}=0$:
--   $$\tilde x_{n+1}=\mathrm{prox}_{\tau G}\big(x_n-\tau\nabla F(x_n)-\tau L^*y_n\big),\qquad \tilde y_{n+1}=\mathrm{prox}_{\sigma H^*}\big(y_n+\sigma L(2\tilde x_{n+1}-x_n)\big).$$
--   Then
--   $$-\begin{pmatrix}\nabla F(x_n)\\0\end{pmatrix}\in A(\tilde z_{n+1})+P(\tilde z_{n+1}-z_n),$$
--   where $A(x,y)=(\partial G(x)+L^*y)\times(-Lx+\partial H^*(y))$ and $P(x,y)=(\tfrac1\tau x-L^*y,\,-Lx+\tfrac1\sigma y)$ is the operator (20). Componentwise, $\tfrac1\tau(x_n-\tilde x_{n+1})-\nabla F(x_n)-L^*y_n\in\partial G(\tilde x_{n+1})$ and $\tfrac1\sigma(y_n-\tilde y_{n+1})+L(2\tilde x_{n+1}-x_n)\in\partial H^*(\tilde y_{n+1})$.
--
--   This inclusion says $\tilde z_{n+1}=(I+P^{-1}\circ A)^{-1}\circ(I-P^{-1}\circ B)(z_n)$ (23) with $B(z)=(\nabla F(x),0)$: the error-free step of Algorithm 3.1 is a forward–backward step in the metric of $P$. With $F=0$ (Theorem 3.2) $B=0$ and it is a resolvent step of $P^{-1}\circ A$, which is how (31) is obtained.
--
--   **Formalization Note** $\mathrm{prox}_{\tau G}$ and $\mathrm{prox}_{\sigma H^*}$ are maps with the published `IsProx` property; $\mathcal Z_I$ is `WithLp 2 (X × Y)` and the inclusion is written as $-(\nabla F(x_n),0)-P(\tilde z_{n+1}-z_n)\in A(\tilde z_{n+1})$, with $P(\tilde z_{n+1}-z_n)$ written out from (20). The standing assumption (2) on $F$ is carried as `IsSmoothTerm β F`.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 10, §4, proof of Theorem 3.1, (22)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_CondatPD_PPA_Setting

namespace CondatPD.PPA

theorem inclusion_22 {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → ℝ) (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (β : ℝ) (hF : IsSmoothTerm β F)
    (hG : ThreeOpSplitting.ConvexRates.IsProperClosedConvex G)
    (hH : ThreeOpSplitting.ConvexRates.IsProperClosedConvex H)
    (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (PG : X → X) (PH : Y → Y)
    (hPG : ThreeOpSplitting.ConvexRates.IsProx τ G PG)
    (hPH : ThreeOpSplitting.ConvexRates.IsProx σ (MoreauProx.Characterization.conj H) PH)
    (xn xt : X) (yn yt : Y)
    (hxt : xt = PG (xn - τ • gradient F xn - τ • ContinuousLinearMap.adjoint L yn))
    (hyt : yt = PH (yn + σ • L ((2 : ℝ) • xt - xn))) :
    -WithLp.toLp 2 (gradient F xn, (0 : Y))
        - WithLp.toLp 2 (τ⁻¹ • (xt - xn) - ContinuousLinearMap.adjoint L (yt - yn),
            -(L (xt - xn)) + σ⁻¹ • (yt - yn))
      ∈ opA G H L (WithLp.toLp 2 (xt, yt)) := by sorry

end CondatPD.PPA
