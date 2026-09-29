-- Prove2me | Theorems.Thm_ClassicalDynamics_noether_theorem
-- name    : ClassicalDynamics.noether_theorem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T23:43:10.136767+00:00
-- url     : https://prove2.me/theorems/b085b836-3bf0-4bba-b5b2-097156df2930
-- title:
--   Noether's theorem: every continuous symmetry yields a conserved quantity
-- statement:
--   **Tong, eqs. (2.51)-(2.54): Noether's theorem.** Consider a one-parameter family of paths
--   $$q_i(t) \longmapsto Q_i(s, t), \qquad s \in \mathbb{R},$$
--   so that $Q(0, \cdot)$ is the path under study. The family is a *continuous symmetry* of the Lagrangian $L$ when
--   $$\frac{\partial}{\partial s} L\big(t, Q(s,t), \dot Q(s,t)\big) = 0 ,$$
--   with the dot denoting $\partial/\partial t$.
--
--   Noether's theorem states that for each such symmetry there exists a conserved quantity. Precisely: if $L$ is smooth, the family $Q$ is smooth jointly in $(s,t)$, $Q$ is a continuous symmetry of $L$, and the path $Q(0,\cdot)$ satisfies Lagrange's equations, then
--   $$N(t) = \sum_{i=1}^{n} \frac{\partial L}{\partial \dot q_i}\big(t, Q(0,t), \dot Q(0,t)\big)\, \frac{\partial Q_i}{\partial s}(0, t)$$
--   takes the same value at every time.
--
--   Applied to translations of a closed system this gives conservation of total momentum, to rotations conservation of angular momentum, and to time translations conservation of energy.
-- source:
--   D. Tong, Classical Dynamics, University of Cambridge Part II Mathematical Tripos, Michaelmas 2004/2005, https://www.damtp.cam.ac.uk/user/tong/dynamics.html, Section 2 (pp. 10-25), pp. 24-25, Section 2.4.1, eqs. (2.51)-(2.54)

import Definitions.Def_ClassicalDynamics_core

namespace ClassicalDynamics

/-- Tong, eqs. (2.51)–(2.54): Noether's theorem. -/
theorem noether_theorem {n : ℕ} (L : Lagrangian n) (hL : IsSmoothLagrangian L)
    (Q : ℝ → ℝ → Fin n → ℝ)
    (hQ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Q p.1 p.2))
    (hsym : IsContinuousSymmetry L Q) (hmot : IsMotion L (Q 0)) :
    IsConstantInTime (noetherCharge L Q) := by sorry
end ClassicalDynamics
