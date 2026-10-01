-- Prove2me | Theorems.Thm_CalamaiMore_QP_algorithm61_terminates
-- name    : CalamaiMore.QP.algorithm61_terminates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:01:00.168187+00:00
-- url     : https://prove2.me/theorems/ca2a55ce-f855-440f-8238-027017db8b35
-- title:
--   Theorem 6.2 — Algorithm 6.1 terminates at a stationary point
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, let
--
--   $$
--   \Omega = \{x \in E : \langle c_j, x\rangle \ge \delta_j,\ j = 1, \dots, m\}
--   $$
--
--   be a polyhedral set, and let $f(x) = \tfrac12\langle x, Qx\rangle + \langle b, x\rangle + c_0$ be a quadratic function ($Q$ self-adjoint, not necessarily positive semidefinite) that is bounded below on $\Omega$. Fix constants $\gamma_1, \gamma_2 > 0$, $\mu_1, \mu_2 \in (0,1)$ and $\gamma_3$, and let $(x_k, W_k, \alpha_k)_{k \ge 0}$ be any run of Algorithm 6.1. Then some iterate is stationary:
--
--   $$
--   \exists\, l \ge 0 : \quad \langle \nabla f(x_l), x - x_l \rangle \ge 0 \quad \text{for all } x \in \Omega.
--   $$
--
--   The theorem gives finite termination of an active-set quadratic programming algorithm without any nondegeneracy assumption and without an anti-cycling rule: the gradient projection step replaces the Lagrange-multiplier test used to leave a working set.
--
--   **Formalization Note** "Algorithm 6.1 terminates at some iterate $x_l$ which is stationary" is rendered as: every run, which is an infinite sequence satisfying the rules of the algorithm at every step, contains a stationary iterate $x_l$ (the algorithm is stopped there). The constants' ranges are those of Section 2; $\gamma_3$ is an arbitrary real, as in (3.2). No bound on $\{x_k\}$ and no nondegeneracy is assumed.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 111, Theorem 6.2

import Mathlib
import Definitions.Def_CalamaiMore_QP_IsQuadratic
import Definitions.Def_CalamaiMore_Shared_IsStationaryPoint
import Definitions.Def_CalamaiMore_QP_IsAlgorithm61Run

namespace CalamaiMore.QP

/-- Calamai–Moré, Theorem 6.2 (p. 111): if `f` is a quadratic function bounded below on the
polyhedral `Ω = {x : ⟨c_j, x⟩ ≥ δ_j, j = 1, …, m}`, then every run of Algorithm 6.1 reaches a
stationary iterate `x_l`. -/
theorem algorithm61_terminates {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ)
    (f : E → ℝ) (hf : IsQuadratic f) (hbdd : BddBelow (f '' polyhedron c δ))
    (γ₁ γ₂ γ₃ μ₁ μ₂ : ℝ) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hμ₁ : μ₁ ∈ Set.Ioo (0 : ℝ) 1) (hμ₂ : μ₂ ∈ Set.Ioo (0 : ℝ) 1)
    (x : ℕ → E) (W : ℕ → Finset (Fin m)) (α : ℕ → ℝ)
    (hrun : IsAlgorithm61Run f c δ γ₁ γ₂ γ₃ μ₁ μ₂ x W α) :
    ∃ l : ℕ, CalamaiMore.Shared.IsStationaryPoint f (polyhedron c δ) (x l) := by sorry

end CalamaiMore.QP
