-- Prove2me | Theorems.Thm_FirstOrderOpt_OperatorSliding_ps_procedure_bound_v2
-- name    : FirstOrderOpt.OperatorSliding.ps_procedure_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:17:27.188596+00:00
-- url     : https://prove2.me/theorems/94e0fcab-f578-44d1-a035-c16e3c3fd3c0
-- title:
--   Proposition 8.1 — convergence of the prox-sliding (PS) procedure (corrected)
-- statement:
--   Let $X$ be closed convex in a real inner-product space, $\nu$ a distance generating function on $X$ with prox-function $V$, $g$ an affine function (the linear model $l_f(\underline x,\cdot)$ of the outer step), $h$ convex with subgradient selector $h'$ and linearization $l_h(y,z)=h(y)+\langle h'(y),z-y\rangle$ satisfying (8.1.3) $h(z)\le l_h(y,z)+M\|z-y\|$, and $\chi$ convex. The procedure $PS(g,x,\beta,T)$ starts from $u_0=\tilde u_0=x\in X$ and sets
--   $$u_t=\arg\min_{u\in X}\big\{g(u)+l_h(u_{t-1},u)+\beta V(x,u)+\beta p_tV(u_{t-1},u)+\chi(u)\big\},\qquad\tilde u_t=(1-\theta_t)\tilde u_{t-1}+\theta_tu_t$$
--   ((8.1.17)–(8.1.18)), with $\Phi(u)=g(u)+h(u)+\beta V(x,u)+\chi(u)$ (8.1.19). If $p_t>0$ and $\theta_t$ satisfy (8.1.20) — $P_0=1$, $P_t=p_t(1+p_t)^{-1}P_{t-1}$, $\theta_t=(P_{t-1}-P_t)/((1-P_t)P_{t-1})$ — then for every $t\ge 1$ and $u\in X$, (8.1.21):
--   $$\frac\beta{1-P_t}V(u_t,u)+\Phi(\tilde u_t)-\Phi(u)\le\frac{P_t}{1-P_t}\Big[\beta V(x,u)+\frac{M^2}{2\beta}\sum_{i=1}^t\frac1{p_i^2P_{i-1}}\Big].$$
--
--   **Formalization Note.** The retired statement dropped the convexity of $g$, $h$ and $\chi$ (needed for Jensen at the averaged point $\tilde u_t$; disproved with a $g$ spiking at $\tilde u_t$), took $V$ free, and assumed the three-point inequality of the PS step as a hypothesis instead of the step itself. $V$ is the prox-function of a distance generating function on $X$; $f$ is convex with $L$-Lipschitz gradient $\nabla f$ tied to $f$; $h$ is convex with subgradients $h'$ satisfying (8.1.3); $\chi$ is convex; $X$ is closed convex. The PS step is stated as the minimization (8.1.17); its three-point consequence (Lemma 3.5) is part of the proof.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 489, Proposition 8.1, with (8.1.3) and (8.1.17)-(8.1.21)

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

namespace FirstOrderOpt.OperatorSliding

open scoped RealInnerProductSpace
open FirstOrderOpt.Prox

/-- Proposition 8.1 (convergence of the prox-sliding PS procedure), Lan p. 489. Let `X` be closed
convex, `ν` a distance generating function on `X` with prox-function `V = ν.V`, `g` an affine
function (the linear model `l_f(x, ·)` of the outer step), `h` convex with subgradients `h'`
satisfying (8.1.3) `h(z) ≤ l_h(y, z) + M‖z - y‖` for `l_h(y, z) := h(y) + ⟨h'(y), z - y⟩`, and
`χ` convex. `PS(g, x, β, T)` runs `u_t = argmin_{u ∈ X} {g(u) + l_h(u_{t-1}, u) + βV(x, u) +
βp_t V(u_{t-1}, u) + χ(u)}` (8.1.17) and `ũ_t = (1 - θ_t)ũ_{t-1} + θ_t u_t` (8.1.18) from
`u_0 = ũ_0 = x`, with `Φ(u) := g(u) + h(u) + βV(x, u) + χ(u)` (8.1.19). If `{p_t}, {θ_t}` satisfy
(8.1.20) (`P_0 = 1`, `P_t = p_t(1 + p_t)⁻¹P_{t-1}`, `θ_t = (P_{t-1} - P_t)/((1 - P_t)P_{t-1})`),
then for every `t ≥ 1` and `u ∈ X`, (8.1.21) holds:
`β(1 - P_t)⁻¹ V(u_t, u) + Φ(ũ_t) - Φ(u) ≤ P_t(1 - P_t)⁻¹ [βV(x, u) + (M²/(2β)) Σ_{i=1}^t
(p_i² P_{i-1})⁻¹]`.

Corrected version: the convexity of `g` (affine), `h` and `χ` — needed for Jensen at the averaged
point `ũ_t` — and the closed convexity of `X` are stated (the retired statement dropped them),
`V` is the Bregman distance of a distance generating function, `l_h` is the linearization of `h`
built from its subgradients, and the PS step is stated as the minimization (8.1.17) itself rather
than as the three-point inequality it implies. -/
theorem ps_procedure_bound_v2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (g : E → ℝ) (lg : E →L[ℝ] ℝ) (cg : ℝ) (hg : ∀ u, g u = lg u + cg)
    (h : E → ℝ) (hhconv : ConvexOn ℝ X h) (h' : E → E →L[ℝ] ℝ)
    (hh' : ∀ y ∈ X, ∀ z ∈ X, h y + (h' y) (z - y) ≤ h z)
    (lh : E → E → ℝ) (hlh : ∀ y z, lh y z = h y + (h' y) (z - y))
    (chi : E → ℝ) (hchiconv : ConvexOn ℝ X chi)
    (x : E) (hx : x ∈ X) (β M : ℝ) (hβ : 0 < β) (hM : 0 < M)
    (hMLip : ∀ y ∈ X, ∀ z ∈ X, h z ≤ lh y z + M * ‖z - y‖)
    (Φ : E → ℝ) (hΦ : ∀ u, Φ u = g u + h u + β * ν.V x u + chi u)
    (p θ P : ℕ → ℝ) (hp : ∀ t, 0 < p t)
    (hP0 : P 0 = 1)
    (hPrec : ∀ t : ℕ, 1 ≤ t → P t = p t * (1 + p t)⁻¹ * P (t - 1))
    (hθ : ∀ t : ℕ, 1 ≤ t → θ t = (P (t - 1) - P t) / ((1 - P t) * P (t - 1)))
    (u ũ : ℕ → E) (hu0 : u 0 = x) (hũ0 : ũ 0 = x) (hmem : ∀ t, u t ∈ X)
    (huMin : ∀ t : ℕ, 1 ≤ t → ∀ w ∈ X,
      g (u t) + lh (u (t - 1)) (u t) + β * ν.V x (u t) + β * p t * ν.V (u (t - 1)) (u t)
          + chi (u t) ≤
        g w + lh (u (t - 1)) w + β * ν.V x w + β * p t * ν.V (u (t - 1)) w + chi w)
    (hũrec : ∀ t : ℕ, 1 ≤ t → ũ t = (1 - θ t) • ũ (t - 1) + θ t • u t)
    (t : ℕ) (ht : 1 ≤ t) (w : E) (hw : w ∈ X) :
    β * (1 - P t)⁻¹ * ν.V (u t) w + (Φ (ũ t) - Φ w) ≤
      P t * (1 - P t)⁻¹ *
        (β * ν.V x w + (M ^ 2 / (2 * β)) * ∑ i ∈ Finset.Icc 1 t, (p i ^ 2 * P (i - 1))⁻¹) := by
  sorry

end FirstOrderOpt.OperatorSliding
