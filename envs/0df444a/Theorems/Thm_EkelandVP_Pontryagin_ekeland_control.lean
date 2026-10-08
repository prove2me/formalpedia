-- Prove2me | Theorems.Thm_EkelandVP_Pontryagin_ekeland_control
-- name    : EkelandVP.Pontryagin.ekeland_control
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T11:27:35.362989+00:00
-- url     : https://prove2.me/theorems/6e7fec69-6e93-48b5-b6e8-8d80256d5252
-- title:
--   (7.15)–(7.16), p. 350 — an ε²-optimal control u_ε with F(u) ≥ F(u_ε) − εδ(u, u_ε) for every control u
-- statement:
--   Assume Ekeland's standing hypotheses of §7: $K$ is a nonempty compact metrizable space, $T > 0$, $x_0 \in \mathbb R^n$, $f$ and its state Jacobian $f_x'$ are continuous on $\mathbb R^n \times K \times [0, T]$ (condition (a)), and $\langle x, f(x, u, t)\rangle \le c(1 + \|x\|^2)$ for some constant $c$ (condition (b)). Let $g : \mathbb R^n \to \mathbb R$ be $C^1$, write $F(u) = g(x(T))$ for the terminal cost of the control $u$ (with $x$ its trajectory), and let $\delta(u, v) = \operatorname{meas}\{t \in [0, T] \mid u(t) \neq v(t)\}$.
--
--   For every $\varepsilon > 0$ there is a measurable control $u_\varepsilon$, with trajectory $x_\varepsilon$, such that
--
--   $$
--   F(u_\varepsilon) \le \inf F + \varepsilon^2, \qquad (7.15)
--   $$
--
--   $$
--   \forall u \in \mathcal U, \qquad F(u) \ge F(u_\varepsilon) - \varepsilon\, \delta(u, u_\varepsilon). \qquad (7.16)
--   $$
--
--   This is Ekeland's variational principle (Theorem 1.1 of the paper) applied on the complete metric space $(\mathcal U, \delta)$ of Lemma 7.2 to the continuous function $F$ of Lemma 7.3, with $\varepsilon^2$ in place of $\varepsilon$ and $\lambda = \varepsilon$. The control $u_\varepsilon$ is the candidate for the approximate maximum principle of Theorem 7.1.
--
--   **Formalization Note** The infimum in (7.15) ranges over all measurable controls; it is stated as "$g(x_\varepsilon(T)) \le g(x(T)) + \varepsilon^2$ for every measurable control $u$ with trajectory $x$", which avoids a real infimum. Nonemptiness of $K$ is added: the page's "$u(t)$ belongs to some compact metrizable set $K$" presupposes it, and with $K$ empty no control exists.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 350, §7, (7.15)–(7.16)

import Mathlib
import Definitions.Def_EkelandVP_Pontryagin_IsTrajectory
import Definitions.Def_EkelandVP_Pontryagin_ctrlDist

namespace EkelandVP.Pontryagin

theorem ekeland_control {n : ℕ} {K : Type*} [TopologicalSpace K] [CompactSpace K]
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
    ∃ (uε : ℝ → K) (xε : ℝ → EuclideanSpace ℝ (Fin n)),
      Measurable uε ∧ IsTrajectory f x₀ T uε xε ∧
      (∀ (u : ℝ → K) (x : ℝ → EuclideanSpace ℝ (Fin n)), Measurable u →
        IsTrajectory f x₀ T u x → g (xε T) ≤ g (x T) + ε ^ 2) ∧
      (∀ (u : ℝ → K) (x : ℝ → EuclideanSpace ℝ (Fin n)), Measurable u →
        IsTrajectory f x₀ T u x → g (xε T) - ε * ctrlDist T u uε ≤ g (x T)) := by sorry

end EkelandVP.Pontryagin
