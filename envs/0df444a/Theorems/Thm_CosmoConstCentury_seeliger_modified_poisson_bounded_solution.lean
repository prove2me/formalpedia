-- Prove2me | Theorems.Thm_CosmoConstCentury_seeliger_modified_poisson_bounded_solution
-- name    : CosmoConstCentury.seeliger_modified_poisson_bounded_solution
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-05T00:38:58.953803+00:00
-- url     : https://prove2.me/theorems/5e7fd49e-ce0e-400a-86a5-403ad4ef6559
-- title:
--   Seeliger's modified Poisson equation (4): the unique bounded solution is the constant $-4\pi G\rho/\lambda$
-- statement:
--   Let $\lambda>0$ be Seeliger's decay constant, $G$ Newton's constant and $\rho$ a constant mass density on $\mathbb R^3$. Let $\Phi$ be a twice continuously differentiable, bounded function on $\mathbb R^3$. Then $\Phi$ solves the modified Poisson equation (4),
--   $$\nabla^2\Phi-\lambda\Phi=4\pi G\rho\quad\text{on }\mathbb R^3,$$
--   if and only if $\Phi$ is the constant function
--   $$\Phi\equiv-\frac{4\pi G\rho}{\lambda}.$$
--
--   In contrast with equation (3), Seeliger's modification yields a well-defined potential for an infinite, uniformly filled universe, and this potential is unique among bounded functions.
-- source:
--   C. O'Raifeartaigh, M. O'Keeffe, W. Nahm, S. Mitton, "One hundred years of the cosmological constant: from 'superfluous stunt' to dark energy", Eur. Phys. J. H 43, 73-117 (2018), https://doi.org/10.1140/epjh/e2017-80061-7; Section 2, p. 75, eqs. (2) and (4).

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

theorem seeliger_modified_poisson_bounded_solution (G ρ lam : ℝ) (hlam : 0 < lam)
    (Φ : EuclideanSpace ℝ (Fin 3) → ℝ) (hΦ : ContDiff ℝ 2 Φ) (hbdd : ∃ M : ℝ, ∀ x, |Φ x| ≤ M) :
    (∀ x, laplacian3 Φ x - lam * Φ x = 4 * Real.pi * G * ρ) ↔
      ∀ x, Φ x = -(4 * Real.pi * G * ρ) / lam := by sorry

end CosmoConstCentury
