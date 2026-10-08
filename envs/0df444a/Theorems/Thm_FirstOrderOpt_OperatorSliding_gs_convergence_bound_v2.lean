-- Prove2me | Theorems.Thm_FirstOrderOpt_OperatorSliding_gs_convergence_bound_v2
-- name    : FirstOrderOpt.OperatorSliding.gs_convergence_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:17:28.756917+00:00
-- url     : https://prove2.me/theorems/62d7a1de-c751-401c-ab35-96145971decb
-- title:
--   Theorem 8.1(a) — convergence of the gradient sliding algorithm, unbounded $X$ (corrected)
-- statement:
--   Let $\Psi=f+h+\chi$ on a closed convex $X$ in a real inner-product space (8.1.1): $f$ convex with $L$-Lipschitz gradient $\nabla f$, $h$ convex with subgradients $h'$ satisfying (8.1.3) $h(z)\le h(y)+\langle h'(y),z-y\rangle+M\|z-y\|$, $\chi$ convex; let $\nu$ be a distance generating function on $X$ with prox-function $V$, and $x^*$ an optimal solution. The gradient sliding algorithm (Algorithm 8.1) starts from $x_0=\bar x_0\in X$ and for $k=1,\dots,N$ sets $\underline x_k=(1-\gamma_k)\bar x_{k-1}+\gamma_kx_{k-1}$, $g_k(u)=f(\underline x_k)+\langle\nabla f(\underline x_k),u-\underline x_k\rangle$, $(x_k,\tilde x_k)=PS(g_k,x_{k-1},\beta_k,T_k)$ — the prox-sliding procedure (8.1.17)–(8.1.18) with parameters $p_t,\theta_t$ satisfying (8.1.20) — and $\bar x_k=(1-\gamma_k)\bar x_{k-1}+\gamma_k\tilde x_k$. Let $\Gamma_1=1$, $\Gamma_k=(1-\gamma_k)\Gamma_{k-1}$ (8.1.32), with $\gamma_1=1$, $\gamma_k\in(0,1)$ for $k\ge 2$, $\beta_k\ge L\gamma_k$ (8.1.25), and the monotonicity condition (8.1.33) $\gamma_k\beta_k/(\Gamma_k(1-P_{T_k}))\le\gamma_{k-1}\beta_{k-1}/(\Gamma_{k-1}(1-P_{T_{k-1}}))$ for $k\ge 2$. Then for every $N\ge 1$, (8.1.34):
--   $$\Psi(\bar x_N)-\Psi(x^*)\le\frac{\Gamma_N\beta_1}{1-P_{T_1}}V(x_0,x^*)+\frac{M^2\Gamma_N}2\sum_{k=1}^N\sum_{i=1}^{T_k}\frac{\gamma_kP_{T_k}}{\Gamma_k\beta_k(1-P_{T_k})p_i^2P_{i-1}}.$$
--
--   **Formalization Note.** The retired statement did not exclude $\gamma_k=1$ for $k\ge 2$, which gives $\Gamma_k=0$ and turns (8.1.33) into Lean's $x/0=0$ junk while the conclusion collapses (disproved); $\gamma_k\in(0,1)$ for $k\ge 2$ is the domain on which (8.1.32)–(8.1.34) are meaningful. The retired statement also assumed Proposition 8.2's recursion (8.1.26) as a hypothesis; the corrected statement restates the GS algorithm in full (outer steps and PS inner loops) so that the recursion is part of the proof. $V$ is the prox-function of a distance generating function on $X$; $f$ is convex with $L$-Lipschitz gradient $\nabla f$ tied to $f$; $h$ is convex with subgradients $h'$ satisfying (8.1.3); $\chi$ is convex; $X$ is closed convex.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 491, Theorem 8.1(a), with Algorithm 8.1 (p. 488), (8.1.17)-(8.1.20), (8.1.25), (8.1.32)-(8.1.34)

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

namespace FirstOrderOpt.OperatorSliding

open scoped RealInnerProductSpace
open FirstOrderOpt.Prox

/-- Theorem 8.1(a) (convergence of the gradient sliding GS algorithm, unbounded-`X` case), Lan
p. 491. Let `Ψ := f + h + χ` on the closed convex `X` (8.1.1): `f` convex with `L`-Lipschitz
gradient `fGrad`, `h` convex with subgradients `h'` satisfying (8.1.3) `h(z) ≤ l_h(y, z) +
M‖z - y‖`, `χ` convex; `ν` a distance generating function on `X` with prox-function `V = ν.V`;
`x*` an optimal solution. Algorithm 8.1 (GS) keeps `x k` and `xbar k` with `x 0 = xbar 0 = x0`
and, for `k = 1, …, N`: `xunder k = (1 - γ k) xbar (k-1) + γ k x (k-1)`, the linear model
`g_k(u) = f(xunder k) + ⟨∇f(xunder k), u - xunder k⟩`, `(x k, xtilde k) = PS(g_k, x (k-1), β k,
T k)` (the prox-sliding procedure (8.1.17)–(8.1.18) with parameters `p, θ` satisfying (8.1.20)),
and `xbar k = (1 - γ k) xbar (k-1) + γ k xtilde k`. Let `Γ` be (8.1.32) (`Γ 1 = 1`,
`Γ k = (1 - γ k)Γ (k-1)`), with `γ 1 = 1`, `γ k ∈ (0, 1)` for `k ≥ 2`, `β k ≥ L γ k` (8.1.25) and
the monotonicity condition (8.1.33). Then for every `N ≥ 1`, (8.1.34):
`Ψ(xbar N) - Ψ(x*) ≤ Γ_N β_1/(1 - P_{T_1}) · V(x0, x*) + (M²Γ_N/2) Σ_{k=1}^N Σ_{i=1}^{T_k}
γ_k P_{T_k} / (Γ_k β_k (1 - P_{T_k}) p_i² P_{i-1})`.

Corrected version: `γ k < 1` for `k ≥ 2` is required (the retired statement allowed `γ k = 1`,
giving `Γ k = 0` and turning (8.1.33) into Lean's `x/0 = 0` junk); `V` is the Bregman distance of
a distance generating function; and the GS algorithm (outer steps and PS inner loops) is stated
in full instead of assuming Proposition 8.2's recursion (8.1.26) as a hypothesis. -/
theorem gs_convergence_bound_v2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (f h chi Ψ : E → ℝ) (hΨ : ∀ u, Ψ u = f u + h u + chi u)
    (L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (fGrad : E → E →L[ℝ] ℝ)
    (hGrad : ∀ x ∈ X, HasFDerivWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (hfconv : ∀ x ∈ X, ∀ y ∈ X, f x + (fGrad x) (y - x) ≤ f y)
    (hhconv : ConvexOn ℝ X h) (h' : E → E →L[ℝ] ℝ)
    (hh' : ∀ y ∈ X, ∀ z ∈ X, h y + (h' y) (z - y) ≤ h z)
    (hMLip : ∀ y ∈ X, ∀ z ∈ X, h z ≤ h y + (h' y) (z - y) + M * ‖z - y‖)
    (hchiconv : ConvexOn ℝ X chi)
    (x0 xstar : E) (hx0 : x0 ∈ X) (hxstar : xstar ∈ X)
    (hxstarOpt : ∀ w ∈ X, Ψ xstar ≤ Ψ w)
    (p θ P : ℕ → ℝ) (hp : ∀ t, 0 < p t) (hP0 : P 0 = 1)
    (hPrec : ∀ t : ℕ, 1 ≤ t → P t = p t * (1 + p t)⁻¹ * P (t - 1))
    (hθ : ∀ t : ℕ, 1 ≤ t → θ t = (P (t - 1) - P t) / ((1 - P t) * P (t - 1)))
    (β γ : ℕ → ℝ) (T : ℕ → ℕ) (hTpos : ∀ k : ℕ, 1 ≤ k → 1 ≤ T k)
    (hβpos : ∀ k : ℕ, 1 ≤ k → 0 < β k)
    (hγ1 : γ 1 = 1) (hγpos : ∀ k : ℕ, 2 ≤ k → 0 < γ k) (hγlt : ∀ k : ℕ, 2 ≤ k → γ k < 1)
    (hβγ : ∀ k : ℕ, 1 ≤ k → L * γ k ≤ β k)
    (Γ : ℕ → ℝ) (hΓ1 : Γ 1 = 1) (hΓrec : ∀ k : ℕ, 2 ≤ k → Γ k = (1 - γ k) * Γ (k - 1))
    (hMono : ∀ k : ℕ, 2 ≤ k →
      γ k * β k / (Γ k * (1 - P (T k))) ≤ γ (k - 1) * β (k - 1) / (Γ (k - 1) * (1 - P (T (k - 1)))))
    (x xbar xunder xtilde : ℕ → E) (hx0eq : x 0 = x0) (hxbar0 : xbar 0 = x0)
    (hxunder : ∀ k : ℕ, 1 ≤ k → xunder k = (1 - γ k) • xbar (k - 1) + γ k • x (k - 1))
    (u ũ : ℕ → ℕ → E)
    (hu0 : ∀ k : ℕ, 1 ≤ k → u k 0 = x (k - 1)) (hũ0 : ∀ k : ℕ, 1 ≤ k → ũ k 0 = x (k - 1))
    (humem : ∀ k t, u k t ∈ X)
    (huMin : ∀ k : ℕ, 1 ≤ k → ∀ t : ℕ, 1 ≤ t → t ≤ T k → ∀ w ∈ X,
      (f (xunder k) + (fGrad (xunder k)) (u k t - xunder k))
          + (h (u k (t - 1)) + (h' (u k (t - 1))) (u k t - u k (t - 1)))
          + β k * ν.V (x (k - 1)) (u k t) + β k * p t * ν.V (u k (t - 1)) (u k t) + chi (u k t) ≤
        (f (xunder k) + (fGrad (xunder k)) (w - xunder k))
          + (h (u k (t - 1)) + (h' (u k (t - 1))) (w - u k (t - 1)))
          + β k * ν.V (x (k - 1)) w + β k * p t * ν.V (u k (t - 1)) w + chi w)
    (hũrec : ∀ k : ℕ, 1 ≤ k → ∀ t : ℕ, 1 ≤ t → t ≤ T k →
      ũ k t = (1 - θ t) • ũ k (t - 1) + θ t • u k t)
    (hxk : ∀ k : ℕ, 1 ≤ k → x k = u k (T k)) (hxtilde : ∀ k : ℕ, 1 ≤ k → xtilde k = ũ k (T k))
    (hxbar : ∀ k : ℕ, 1 ≤ k → xbar k = (1 - γ k) • xbar (k - 1) + γ k • xtilde k)
    (N : ℕ) (hN : 1 ≤ N) :
    Ψ (xbar N) - Ψ xstar ≤
      Γ N * β 1 / (1 - P (T 1)) * ν.V x0 xstar
        + M ^ 2 * Γ N / 2 *
            ∑ k ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc 1 (T k),
              γ k * P (T k) / (Γ k * β k * (1 - P (T k)) * p i ^ 2 * P (i - 1)) := by sorry

end FirstOrderOpt.OperatorSliding
