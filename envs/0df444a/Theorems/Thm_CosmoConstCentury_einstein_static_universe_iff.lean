-- Prove2me | Theorems.Thm_CosmoConstCentury_einstein_static_universe_iff
-- name    : CosmoConstCentury.einstein_static_universe_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T01:40:41.619371+00:00
-- url     : https://prove2.me/theorems/2a8eccb0-0d91-48a8-ad7a-b06b09a25bd1
-- title:
--   Einstein's static universe (eq. 10): $\Lambda=\kappa c^2\rho/2=c^2/R^2$
-- statement:
--   Let $R_0>0$ and $\rho_0$ be constants, and let $G$, $c$, $\Lambda$ be arbitrary real constants with $\kappa=8\pi G/c^2$. The constant scale factor $R(t)\equiv R_0$ together with the constant density $\rho(t)\equiv\rho_0$ solves the closed ($k=1$) Friedmann–Lemaître dust equations (15)–(16) for all times if and only if
--   $$\Lambda=\frac{\kappa c^2\rho_0}{2}\qquad\text{and}\qquad\Lambda=\frac{c^2}{R_0^2}.$$
--
--   In units with $c=1$ this is Einstein's 1917 relation (10), $\lambda=\kappa\rho/2=1/R^2$, linking the cosmological constant, the mean density and the radius of the static closed universe.
--
--   **Formalization Note** The predicate `IsFriedmannSolution G c Λ k I R ρ` requires, at every $t\in I$, that $R(t)>0$, that $R$ is $C^2$ in a neighbourhood of $t$, and that the two equations hold with $\kappa=8\pi G/c^2$.
-- source:
--   C. O'Raifeartaigh, M. O'Keeffe, W. Nahm, S. Mitton, "One hundred years of the cosmological constant: from 'superfluous stunt' to dark energy", Eur. Phys. J. H 43, 73-117 (2018), https://doi.org/10.1140/epjh/e2017-80061-7; Section 3, p. 78, eq. (10) (Einstein 1917); field equations (9) p. 77; Friedmann form (15)-(16) p. 82.

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

theorem einstein_static_universe_iff (G c Λ R₀ ρ₀ : ℝ) (hR₀ : 0 < R₀) :
    IsFriedmannSolution G c Λ 1 Set.univ (fun _ => R₀) (fun _ => ρ₀) ↔
      (Λ = einsteinKappa G c * c ^ 2 * ρ₀ / 2 ∧ Λ = c ^ 2 / R₀ ^ 2) := by sorry

end CosmoConstCentury
