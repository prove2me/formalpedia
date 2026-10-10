-- Prove2me | Theorems.Thm_ConservationLaws_nbody_momentum_and_energy_conservation
-- name    : ConservationLaws.nbody_momentum_and_energy_conservation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:25:30.282744+00:00
-- url     : https://prove2.me/theorems/f1dd1af3-4825-4e88-b716-f68ad44452c1
-- title:
--   Isolated $N$-body system with pair potentials: momentum and energy are conserved
-- statement:
--   Let $N$ particles in $\mathbb{R}^d$ with masses $m_i > 0$ interact only through pair potentials $\varphi_{ij} = \varphi_{ji}$, each differentiable on $(0,\infty)$, so that along a collision-free trajectory ($x_i(t) \ne x_j(t)$ for $i \ne j$) Newton's second law reads
--   $$m_i\,\ddot x_i(t) = \sum_{j \ne i} -\varphi_{ij}'\big(\|x_i(t)-x_j(t)\|\big)\,\frac{x_i(t)-x_j(t)}{\|x_i(t)-x_j(t)\|}.$$
--   Then the total momentum $\sum_i m_i \dot x_i(t)$ and the total mechanical energy
--   $$E(t) = \sum_i \tfrac12 m_i\|\dot x_i(t)\|^2 + \sum_{i<j}\varphi_{ij}\big(\|x_i(t)-x_j(t)\|\big)$$
--   are both constant in time.
-- source:
--   Wikipedia, "Momentum" (uploaded PDF), https://en.wikipedia.org/wiki/Momentum, section "Conservation"; Wikipedia, "Conservation of energy" (uploaded PDF), https://en.wikipedia.org/wiki/Conservation_of_energy (conservation of kinetic plus potential energy in a closed system)

import Mathlib

namespace ConservationLaws

theorem nbody_momentum_and_energy_conservation
    {d N : ℕ} (m : Fin N → ℝ) (hm : ∀ i, 0 < m i)
    (φ : Fin N → Fin N → ℝ → ℝ) (hφsym : ∀ i j, φ i j = φ j i)
    (hφdiff : ∀ i j, ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (φ i j) r)
    (x v a : Fin N → ℝ → EuclideanSpace ℝ (Fin d))
    (hnc : ∀ t i j, i ≠ j → x i t ≠ x j t)
    (hx : ∀ i t, HasDerivAt (x i) (v i t) t)
    (hv : ∀ i t, HasDerivAt (v i) (a i t) t)
    (hnewton : ∀ i t, m i • a i t = ∑ j ∈ Finset.univ.erase i,
      (-(deriv (φ i j) ‖x i t - x j t‖) / ‖x i t - x j t‖) • (x i t - x j t)) :
    (∀ t s, ∑ i, m i • v i t = ∑ i, m i • v i s) ∧
    (∀ t s,
      (∑ i, (1 / 2 : ℝ) * m i * ‖v i t‖ ^ 2 + ∑ i, ∑ j ∈ Finset.Ioi i, φ i j ‖x i t - x j t‖) =
      (∑ i, (1 / 2 : ℝ) * m i * ‖v i s‖ ^ 2 + ∑ i, ∑ j ∈ Finset.Ioi i, φ i j ‖x i s - x j s‖)) := by sorry

end ConservationLaws
