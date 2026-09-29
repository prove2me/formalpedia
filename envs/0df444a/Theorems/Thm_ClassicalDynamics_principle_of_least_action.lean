-- Prove2me | Theorems.Thm_ClassicalDynamics_principle_of_least_action
-- name    : ClassicalDynamics.principle_of_least_action
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T23:36:29.052188+00:00
-- url     : https://prove2.me/theorems/b3d1975c-4f9b-4040-a0bc-53d4500ea81c
-- title:
--   Principle of least action: $\delta S = 0 \iff$ Lagrange's equations
-- statement:
--   **Tong, eq. (2.8).** Let $L$ be a smooth Lagrangian on $\mathbb{R}^n$, let $q : \mathbb{R} \to \mathbb{R}^n$ be a smooth path, and let $t_1 < t_2$.
--
--   Then the action
--   $$S[q] = \int_{t_1}^{t_2} L\big(t, q(t), \dot q(t)\big)\, dt$$
--   is stationary at $q$ with respect to every smooth variation vanishing at the endpoints — that is, for every smooth $h$ with $h(t_1) = h(t_2) = 0$ the function $s \mapsto S[q + s h]$ is differentiable at $s = 0$ with derivative $0$ — if and only if $q$ satisfies Lagrange's equations
--   $$\frac{d}{dt}\left(\frac{\partial L}{\partial \dot q_i}\right) = \frac{\partial L}{\partial q_i}$$
--   at every interior time $t \in (t_1, t_2)$ and in every coordinate $i$.
--
--   This is the statement Tong derives by varying the path, integrating by parts, and discarding the boundary term; the reverse implication is the elementary direction.
-- source:
--   D. Tong, Classical Dynamics, University of Cambridge Part II Mathematical Tripos, Michaelmas 2004/2005, https://www.damtp.cam.ac.uk/user/tong/dynamics.html, Section 2 (pp. 10-25), pp. 10-11, eqs. (2.5)-(2.8) (Theorem: Principle of Least Action)

import Definitions.Def_ClassicalDynamics_core

namespace ClassicalDynamics

/-- Tong, eq. (2.8): the principle of least action. -/
theorem principle_of_least_action {n : ℕ} (L : Lagrangian n)
    (hL : IsSmoothLagrangian L) (q : ℝ → Fin n → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (t₁ t₂ : ℝ) (ht : t₁ < t₂) :
    (∀ h : ℝ → Fin n → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → h t₁ = 0 → h t₂ = 0 →
        HasDerivAt (fun s : ℝ => action L (fun t => q t + s • h t) t₁ t₂) 0 0)
      ↔ (∀ (i : Fin n), ∀ t ∈ Set.Ioo t₁ t₂,
          HasDerivAt (fun s : ℝ => dLdv L i s (q s) (vel q s))
            (dLdq L i t (q t) (vel q t)) t) := by sorry
end ClassicalDynamics
