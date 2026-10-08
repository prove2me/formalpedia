-- Prove2me | Theorems.Thm_CosmoConstCentury_einstein_newtonian_limit_bounded_iff
-- name    : CosmoConstCentury.einstein_newtonian_limit_bounded_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T02:10:35.160533+00:00
-- url     : https://prove2.me/theorems/00f50d29-55d1-4bd7-b416-54122ec89d38
-- title:
--   Newtonian limit (11) of Einstein's modified equations: a bounded potential exists iff $c^2\Lambda=4\pi G\rho$
-- statement:
--   Let $G$, $c$, $\Lambda$ be real constants and let $\rho$ be a constant mass density on $\mathbb R^3$. The Newtonian limit of Einstein's modified field equations is equation (11) of the review,
--   $$\nabla^2\phi+c^2\Lambda=4\pi G\rho .$$
--   This equation has a bounded, twice continuously differentiable solution $\phi$ on $\mathbb R^3$ if and only if
--   $$c^2\Lambda=4\pi G\rho .$$
--
--   Thus, unlike Seeliger's equation (4), equation (11) admits a finite potential for a uniform infinite distribution of matter only for one exact balance between the density and the cosmological constant; this is the discrepancy between (4) and (11) noted in Section 3.1.
-- source:
--   C. O'Raifeartaigh, M. O'Keeffe, W. Nahm, S. Mitton, "One hundred years of the cosmological constant: from 'superfluous stunt' to dark energy", Eur. Phys. J. H 43, 73-117 (2018), https://doi.org/10.1140/epjh/e2017-80061-7; Section 3.1, p. 80, eq. (11) compared with eq. (4).

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

theorem einstein_newtonian_limit_bounded_iff (G c Λ ρ : ℝ) :
    (∃ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 2 φ ∧ (∃ M : ℝ, ∀ x, |φ x| ≤ M) ∧
      ∀ x, laplacian3 φ x + c ^ 2 * Λ = 4 * Real.pi * G * ρ) ↔
    c ^ 2 * Λ = 4 * Real.pi * G * ρ := by sorry

end CosmoConstCentury
