-- Prove2me | Theorems.Thm_EkelandVP_Pontryagin_trajectory_bound
-- name    : EkelandVP.Pontryagin.trajectory_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T11:26:21.394405+00:00
-- url     : https://prove2.me/theorems/79d2f6ad-432a-4d48-9c0a-eb7f22011694
-- title:
--   (7.2), p. 348 — Gronwall a priori bound ‖x(t)‖² ≤ (‖x₀‖² + 2cT)e^{2cT} on trajectories
-- statement:
--   Let $K$ be a compact metrizable space and $T > 0$. Let $f : \mathbb R^n \times K \times \mathbb R \to \mathbb R^n$ be continuous on $\mathbb R^n \times K \times [0, T]$, and suppose there is a constant $c$ with
--
--   $$
--   \langle x, f(x, u, t)\rangle \le c\,(1 + \|x\|^2) \qquad \text{for all } x \in \mathbb R^n,\ u \in K,\ t \in [0, T]
--   $$
--
--   (Ekeland's condition (b)). Let $u : \mathbb R \to K$ be a measurable control and let $x$ be a trajectory of $\dot x = f(x, u, t)$, $x(0) = x_0$, on $[0, T]$. Then
--
--   $$
--   \|x(t)\|^2 \le \left(\|x_0\|^2 + 2cT\right) e^{2cT} \qquad \text{for every } t \in [0, T]. \qquad (7.2)
--   $$
--
--   This a priori estimate keeps every trajectory inside a fixed ball, independently of the control; it gives global existence of trajectories on $[0, T]$ and the compactness used later in Lemma 7.3.
--
--   **Formalization Note** Condition (b) evaluated at $x = 0$ forces $c \ge 0$, so no sign hypothesis on $c$ is added. The page prints the arguments of $f$ in (b) as $f(t, x, u)$; everywhere else in §7 they are $f(x, u, t)$, which is the order used here. Trajectories are in integral form (definition `IsTrajectory`).
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 348, §7, (7.2)

import Mathlib
import Definitions.Def_EkelandVP_Pontryagin_IsTrajectory

namespace EkelandVP.Pontryagin

theorem trajectory_bound {n : ℕ} {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K]
    (T : ℝ) (hT : 0 < T) (x₀ : EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → K → ℝ → EuclideanSpace ℝ (Fin n))
    (hf : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) × K × ℝ => f z.1 z.2.1 z.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T))
    (c : ℝ) (hc : ∀ (x : EuclideanSpace ℝ (Fin n)) (u : K), ∀ t ∈ Set.Icc 0 T,
      inner ℝ x (f x u t) ≤ c * (1 + ‖x‖ ^ 2))
    (u : ℝ → K) (hu : Measurable u) (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hx : IsTrajectory f x₀ T u x) :
    ∀ t ∈ Set.Icc 0 T, ‖x t‖ ^ 2 ≤ (‖x₀‖ ^ 2 + 2 * c * T) * Real.exp (2 * c * T) := by sorry

end EkelandVP.Pontryagin
