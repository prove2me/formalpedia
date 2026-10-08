-- Prove2me | Theorems.Thm_EkelandVP_Pontryagin_lemma_7_4
-- name    : EkelandVP.Pontryagin.lemma_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T11:28:10.654994+00:00
-- url     : https://prove2.me/theorems/8f947013-bf43-47b2-b0f6-03155fdeccb6
-- title:
--   Lemma 7.4, p. 351 — the needle derivative (d/dτ) g(x_τ(T))|_{τ=0} = ⟨f(x_ε(t₀), u₀, t₀) − f(x_ε(t₀), u_ε(t₀), t₀), p_ε(t₀)⟩
-- statement:
--   Assume Ekeland's standing hypotheses of §7: $K$ is a compact metrizable space, $T > 0$, $x_0 \in \mathbb R^n$, $f$ and its state Jacobian $f_x'$ are continuous on $\mathbb R^n \times K \times [0, T]$ (condition (a)), and $\langle x, f(x, u, t)\rangle \le c(1 + \|x\|^2)$ for some constant $c$ (condition (b)). Let $g : \mathbb R^n \to \mathbb R$ be $C^1$.
--
--   Let $u_\varepsilon$ be a measurable control with trajectory $x_\varepsilon$, and let $p_\varepsilon$ solve the adjoint equation $\dot p_\varepsilon = -{}^t f_x'(x_\varepsilon, u_\varepsilon, t)\, p_\varepsilon$, $p_\varepsilon(T) = g'(x_\varepsilon(T))$. Take $t_0 \in\, ]0, T[$ at which the state equation holds, i.e. $x_\varepsilon$ is differentiable at $t_0$ with $\dot x_\varepsilon(t_0) = f(x_\varepsilon(t_0), u_\varepsilon(t_0), t_0)$, and take $u_0 \in K$. As in (7.18), for $\tau \ge 0$ let
--
--   $$
--   v_\tau(t) = u_0 \ \text{ if } t \in [0, T] \cap\, ]t_0 - \tau, t_0[, \qquad v_\tau(t) = u_\varepsilon(t) \ \text{ otherwise},
--   $$
--
--   and let $x_\tau$ be the trajectory of $v_\tau$ (for $0 \le \tau \le t_0$). Then $\tau \mapsto g(x_\tau(T))$ has a right derivative at $\tau = 0$, and
--
--   $$
--   \frac{d}{d\tau}\, g(x_\tau(T))\Big|_{\tau = 0} = \big\langle f(x_\varepsilon(t_0), u_0, t_0) - f(x_\varepsilon(t_0), u_\varepsilon(t_0), t_0),\ p_\varepsilon(t_0) \big\rangle.
--   $$
--
--   This first-order expansion of the terminal cost under a needle variation, combined with (7.16), yields the approximate maximum condition (7.5) of Theorem 7.1.
--
--   **Formalization Note** The derivative is one-sided (within $[0, t_0]$ at $0$), because $v_\tau$ is defined for $\tau \ge 0$ only. The lemma is classical and does not use the optimality properties (7.15)–(7.16), so it is stated for an arbitrary measurable control $u_\varepsilon$. "Where the equality holds" (in (7.17)) is the hypothesis that $x_\varepsilon$ has derivative $f(x_\varepsilon(t_0), u_\varepsilon(t_0), t_0)$ at $t_0$. Trajectories and adjoint solutions are in integral form (definitions `IsTrajectory`, `IsAdjoint`).
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 351, Lemma 7.4 (needle variation (7.18), p. 350)

import Mathlib
import Definitions.Def_EkelandVP_Pontryagin_IsTrajectory
import Definitions.Def_EkelandVP_Pontryagin_IsAdjoint
import Definitions.Def_EkelandVP_Pontryagin_needle

namespace EkelandVP.Pontryagin

theorem lemma_7_4 {n : ℕ} {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K]
    (T : ℝ) (hT : 0 < T) (x₀ : EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → K → ℝ → EuclideanSpace ℝ (Fin n))
    (fx : EuclideanSpace ℝ (Fin n) → K → ℝ →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hf : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) × K × ℝ => f z.1 z.2.1 z.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T))
    (hfx : ∀ (x : EuclideanSpace ℝ (Fin n)) (u : K), ∀ t ∈ Set.Icc 0 T,
      HasFDerivAt (fun y => f y u t) (fx x u t) x)
    (hfxc : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) × K × ℝ => fx z.1 z.2.1 z.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T))
    (hb : ∃ c : ℝ, ∀ (x : EuclideanSpace ℝ (Fin n)) (u : K), ∀ t ∈ Set.Icc 0 T,
      inner ℝ x (f x u t) ≤ c * (1 + ‖x‖ ^ 2))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 1 g)
    (uε : ℝ → K) (huε : Measurable uε) (xε pε : ℝ → EuclideanSpace ℝ (Fin n))
    (hxε : IsTrajectory f x₀ T uε xε) (hpε : IsAdjoint fx g T uε xε pε)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo 0 T) (hderiv : HasDerivAt xε (f (xε t₀) (uε t₀) t₀) t₀)
    (u₀ : K) (X : ℝ → ℝ → EuclideanSpace ℝ (Fin n))
    (hX : ∀ τ ∈ Set.Icc 0 t₀, IsTrajectory f x₀ T (needle T uε u₀ t₀ τ) (X τ)) :
    HasDerivWithinAt (fun τ => g (X τ T))
      (inner ℝ (f (xε t₀) u₀ t₀ - f (xε t₀) (uε t₀) t₀) (pε t₀)) (Set.Icc 0 t₀) 0 := by sorry

end EkelandVP.Pontryagin
