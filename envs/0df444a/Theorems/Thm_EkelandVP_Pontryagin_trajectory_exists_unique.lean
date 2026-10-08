-- Prove2me | Theorems.Thm_EkelandVP_Pontryagin_trajectory_exists_unique
-- name    : EkelandVP.Pontryagin.trajectory_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T11:26:39.307023+00:00
-- url     : https://prove2.me/theorems/a38f5f6a-5f8c-46de-af56-dbe58fec692c
-- title:
--   §7, p. 348 — every measurable control has a unique trajectory on the whole interval [0, T]
-- statement:
--   Let $K$ be a compact metrizable space, $T > 0$ and $x_0 \in \mathbb R^n$. Let $f : \mathbb R^n \times K \times \mathbb R \to \mathbb R^n$ be differentiable in its first variable on $\mathbb R^n \times K \times [0, T]$, with Jacobian $f_x'$, and assume Ekeland's standing hypotheses:
--
--   1. (a) $f$ and $f_x' = (\partial f / \partial x_1, \dots, \partial f / \partial x_n)$ are continuous on $\mathbb R^n \times K \times [0, T]$;
--   2. (b) $\langle x, f(x, u, t)\rangle \le c\,(1 + \|x\|^2)$ for some constant $c$ and all $x \in \mathbb R^n$, $u \in K$, $t \in [0, T]$.
--
--   Then for every measurable control $u : \mathbb R \to K$ the system
--
--   $$
--   \frac{dx}{dt}(t) = f(x(t), u(t), t) \ \text{a.e.}, \qquad x(0) = x_0
--   $$
--
--   has a trajectory $x$ on $[0, T]$, and any two trajectories driven by $u$ coincide on $[0, T]$.
--
--   Existence and uniqueness make "the trajectory corresponding to $u$" well defined, so that the terminal cost $u \mapsto g(x(T))$ of §7 is a function of the control.
--
--   **Formalization Note** Trajectories are in integral form (definition `IsTrajectory`). Hypothesis (a) is stated as: $f$ is jointly continuous on $\mathbb R^n \times K \times [0, T]$, $f(\cdot, u, t)$ has Fréchet derivative $f_x'(x, u, t)$ at every $x$, and $f_x'$ is jointly continuous; this is equivalent to continuity of the partial derivatives $\partial f / \partial x_i$. The constant $c$ of (b) is existentially quantified, as in "for some constant $c$".
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 348, §7, paragraph containing (7.2)

import Mathlib
import Definitions.Def_EkelandVP_Pontryagin_IsTrajectory

namespace EkelandVP.Pontryagin

theorem trajectory_exists_unique {n : ℕ} {K : Type*} [TopologicalSpace K] [CompactSpace K]
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
    (u : ℝ → K) (hu : Measurable u) :
    ∃ x : ℝ → EuclideanSpace ℝ (Fin n), IsTrajectory f x₀ T u x ∧
      ∀ y : ℝ → EuclideanSpace ℝ (Fin n), IsTrajectory f x₀ T u y →
        ∀ t ∈ Set.Icc 0 T, y t = x t := by sorry

end EkelandVP.Pontryagin
