-- Prove2me | Theorems.Thm_EkelandVP_Pontryagin_theorem_7_1
-- name    : EkelandVP.Pontryagin.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T11:26:51.588112+00:00
-- url     : https://prove2.me/theorems/4dfc8f28-ed82-4f63-aec7-ff07ac1d741c
-- title:
--   Theorem 7.1, pp. 348–349 — ε-optimal controls satisfying the Pontryagin maximum principle up to ε
-- statement:
--   Consider the control system
--
--   $$
--   \frac{dx}{dt}(t) = f(x(t), u(t), t) \ \text{a.e.}, \qquad x(0) = x_0 \in \mathbb R^n, \qquad (7.1)
--   $$
--
--   with controls $u(t)$ in a nonempty compact metrizable space $K$ and a horizon $T > 0$, and assume:
--
--   1. (a) $f$ and $f_x' = (\partial f/\partial x_1, \dots, \partial f/\partial x_n)$ are continuous on $\mathbb R^n \times K \times [0, T]$;
--   2. (b) $\langle x, f(x, u, t)\rangle \le c\,(1 + \|x\|^2)$ for some constant $c$.
--
--   Let $g : \mathbb R^n \to \mathbb R$ be $C^1$; the problem is to minimize the terminal cost $g(x(T))$ over all measurable controls $u$.
--
--   **Theorem.** For every $\varepsilon > 0$ there exists a measurable control $u_\varepsilon$, with corresponding trajectory $x_\varepsilon$, such that
--
--   $$
--   g(x_\varepsilon(T)) \le \inf g(x(T)) + \varepsilon, \qquad (7.4)
--   $$
--
--   $$
--   \langle f(x_\varepsilon(t), u_\varepsilon(t), t), p_\varepsilon(t)\rangle \le \min_{u \in K} \langle f(x_\varepsilon(t), u, t), p_\varepsilon(t)\rangle + \varepsilon \quad \text{for almost every } t \in [0, T], \qquad (7.5)
--   $$
--
--   where $p_\varepsilon$ is the solution of the linear differential equation
--
--   $$
--   \frac{dp_\varepsilon}{dt}(t) = -{}^t f_x'(x_\varepsilon(t), u_\varepsilon(t), t)\, p_\varepsilon(t), \qquad p_\varepsilon(T) = g'(x_\varepsilon(T)). \qquad (7.6)
--   $$
--
--   The infimum in (7.4) ranges over the terminal states of all trajectories of (7.1) driven by measurable controls. The theorem asserts an approximate Pontryagin maximum principle that holds whether or not an optimal control exists.
--
--   **Formalization Note**
--   1. The page prints (7.5) with "$\times\, \varepsilon$"; the last step of the proof, (7.21) on p. 351, gives $\langle f(x_\varepsilon(t_0), u_0, t_0) - f(x_\varepsilon(t_0), u_\varepsilon(t_0), t_0), p_\varepsilon(t_0)\rangle \ge -\varepsilon$, i.e. "$+\,\varepsilon$", which is what is stated.
--   2. Since $K$ is compact and $f$ continuous in $u$, the minimum over $K$ is attained, and "$\le \min_{u \in K} \dots + \varepsilon$" is stated equivalently as "$\le \langle f(x_\varepsilon(t), w, t), p_\varepsilon(t)\rangle + \varepsilon$ for every $w \in K$", with one exceptional null set for all $w$.
--   3. (7.4) is stated as "$g(x_\varepsilon(T)) \le g(x(T)) + \varepsilon$ for every measurable control $u$ with trajectory $x$", avoiding a real infimum.
--   4. Trajectories and the adjoint equation are in integral form (definitions `IsTrajectory`, `IsAdjoint`); trajectories are unique, so the existential $x_\varepsilon$ is "the corresponding trajectory". Hypothesis (a) is stated through the Fréchet derivative of $f$ in $x$ and joint continuity of $f$ and $f_x'$, which is equivalent to continuity of the partial derivatives. The page writes $f(t, x, u)$ in (b), a slip for $f(x, u, t)$.
--   5. Nonemptiness of $K$ is added: with $K$ empty there is no control.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), pp. 348–349, Theorem 7.1, (7.4)–(7.6); setting (7.1), (a), (b) on p. 348

import Mathlib
import Definitions.Def_EkelandVP_Pontryagin_IsTrajectory
import Definitions.Def_EkelandVP_Pontryagin_IsAdjoint
open MeasureTheory

namespace EkelandVP.Pontryagin

theorem theorem_7_1 {n : ℕ} {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K] [Nonempty K]
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
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 1 g) (ε : ℝ) (hε : 0 < ε) :
    ∃ uε : ℝ → K, Measurable uε ∧ ∃ xε pε : ℝ → EuclideanSpace ℝ (Fin n),
      IsTrajectory f x₀ T uε xε ∧ IsAdjoint fx g T uε xε pε ∧
      (∀ (u : ℝ → K) (x : ℝ → EuclideanSpace ℝ (Fin n)), Measurable u →
        IsTrajectory f x₀ T u x → g (xε T) ≤ g (x T) + ε) ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), ∀ w : K,
        inner ℝ (f (xε t) (uε t) t) (pε t) ≤ inner ℝ (f (xε t) w t) (pε t) + ε := by sorry

end EkelandVP.Pontryagin
