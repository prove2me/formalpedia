-- Prove2me | Theorems.Thm_CubicNewton_GradDom_theorem7
-- name    : CubicNewton.GradDom.theorem7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:31:37.171982+00:00
-- url     : https://prove2.me/theorems/4863fb98-66ef-4e0c-8589-52e86d320778
-- title:
--   Theorem 7 — linear, then superlinear convergence of cubic Newton on gradient dominated functions of degree 2
-- statement:
--   Let $F \subseteq \mathbb{R}^n$ be a closed convex set and $f$ twice differentiable on $F$ with Hessian Lipschitz on $F$ with constant $L > 0$. Let $x_0 \in \operatorname{int} F$ with $\{x : f(x) \le f(x_0)\} \subseteq \operatorname{int} F$. Suppose $f$ is gradient dominated of degree $2$ on $F$: it attains its minimum over $F$ at $x^* \in F$ and, for a constant $\tau_f > 0$, $f(x) - f(x^*) \le \tau_f \|f'(x)\|^2$ for all $x \in F$. Let $0 < L_0 \le L$ and let $(x_k, M_k)_{k \ge 0}$ be any run of the cubic regularization of Newton method (3.3) from $x_0$. Write $\Delta_k = f(x_k) - f(x^*)$ and
--   $$\tilde\omega = \frac{L_0^4}{324 (L + L_0)^6 \tau_f^3}, \qquad \sigma = \frac{\tilde\omega^{1/4}}{\tilde\omega^{1/4} + \Delta_0^{1/4}} .$$
--
--   1. If $\Delta_0 \ge \tilde\omega$ (4.14), then throughout the first phase — every $k$ such that $\Delta_j \ge \tilde\omega$ for all $j < k$, which runs up to and including the first iteration $k_0$ at which (4.14) fails —
--   $$\Delta_k \le \Delta_0\, e^{-k\sigma} . \qquad (4.15)$$
--   2. For every $k_0$ with $\Delta_{k_0} < \tilde\omega$ and every $k \ge k_0$,
--   $$\Delta_{k+1} \le \tilde\omega \left(\frac{\Delta_k}{\tilde\omega}\right)^{4/3} . \qquad (4.16)$$
--
--   The first phase is linear with a rate depending polynomially on the initial gap; the second is superlinear of order $4/3$. No convexity is assumed and the minimizer need not be unique.
--
--   **Formalization Note** The phase of item 2 is stated for every $k_0$ with $\Delta_{k_0} < \tilde\omega$, not only the first; since $\Delta_k$ is non-increasing along a run this is equivalent. Fractional powers are `Real.rpow` of nonnegative numbers.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 194, Theorem 7, (4.14)–(4.16)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun
import Definitions.Def_CubicNewton_GradDom_IsGradDominated2
import Definitions.Def_CubicNewton_GradDom_omegaTilde

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

/-- Nesterov–Polyak 2006, Theorem 7, p. 194: method (3.3) on a gradient dominated function of
degree `p = 2`. Write `Δ_k = f(x_k) − f(x*)`, `ω̃ = L₀⁴ / (324 (L + L₀)⁶ τ_f³)` (4.14) and
`σ = ω̃^{1/4} / (ω̃^{1/4} + Δ₀^{1/4})`.
1. If `Δ₀ ≥ ω̃` (4.14), then during the first phase — every iteration `k` such that (4.14) holds
   at all earlier iterations `j < k`, i.e. up to and including the first iteration `k₀` at which
   (4.14) fails — `Δ_k ≤ Δ₀ · e^{−kσ}` (4.15).
2. For every `k₀` at which (4.14) fails, i.e. `Δ_{k₀} < ω̃`, and every `k ≥ k₀`:
   `Δ_{k+1} ≤ ω̃ · (Δ_k / ω̃)^{4/3}` (4.16). (The run is monotone, so this is the same as asking
   it from the first such `k₀` on.) -/
theorem theorem7 {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (τ : ℝ) (xs : EuclideanSpace ℝ (Fin n)) (hdom : IsGradDominated2 F f g τ xs)
    (L₀ : ℝ) (hL₀ : 0 < L₀) (hL₀L : L₀ ≤ L)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M) :
    let ω := omegaTilde L₀ L τ
    let Δ : ℕ → ℝ := fun k => f (x k) - f xs
    let σ := ω ^ (1 / 4 : ℝ) / (ω ^ (1 / 4 : ℝ) + Δ 0 ^ (1 / 4 : ℝ))
    (ω ≤ Δ 0 → ∀ k : ℕ, (∀ j < k, ω ≤ Δ j) → Δ k ≤ Δ 0 * Real.exp (-(k * σ))) ∧
      (∀ k₀ : ℕ, Δ k₀ < ω → ∀ k : ℕ, k₀ ≤ k → Δ (k + 1) ≤ ω * (Δ k / ω) ^ (4 / 3 : ℝ)) := by sorry

end CubicNewton.GradDom
