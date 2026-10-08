-- Prove2me | Theorems.Thm_CosmoConstCentury_seeliger_poisson_no_bounded_potential
-- name    : CosmoConstCentury.seeliger_poisson_no_bounded_potential
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-05T00:15:24.936985+00:00
-- url     : https://prove2.me/theorems/947f3099-16e5-4a06-80db-4f0378b815ac
-- title:
--   Seeliger's paradox: the Poisson equation (3) has no bounded potential for a uniform non-zero density
-- statement:
--   Let $G\neq0$ and let $\rho\neq0$ be a constant mass density filling all of Euclidean space $\mathbb R^3$. Then the Poisson equation (3) of the review,
--   $$\nabla^2\Phi=4\pi G\rho\quad\text{on }\mathbb R^3,$$
--   has no solution $\Phi$ that is twice continuously differentiable and bounded.
--
--   This is the mathematical form of the difficulty noted by Seeliger: in an infinite, uniformly filled Newtonian universe the gravitational potential cannot be a finite, well-defined (bounded) function.
-- source:
--   C. O'Raifeartaigh, M. O'Keeffe, W. Nahm, S. Mitton, "One hundred years of the cosmological constant: from 'superfluous stunt' to dark energy", Eur. Phys. J. H 43, 73-117 (2018), https://doi.org/10.1140/epjh/e2017-80061-7; Section 2, p. 75, eq. (3) and surrounding discussion.

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

theorem seeliger_poisson_no_bounded_potential (G ρ : ℝ) (hG : G ≠ 0) (hρ : ρ ≠ 0) :
    ¬ ∃ Φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 2 Φ ∧ (∃ M : ℝ, ∀ x, |Φ x| ≤ M) ∧
      ∀ x, laplacian3 Φ x = 4 * Real.pi * G * ρ := by sorry

end CosmoConstCentury
