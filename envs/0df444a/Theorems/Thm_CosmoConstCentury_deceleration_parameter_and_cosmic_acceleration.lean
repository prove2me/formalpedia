-- Prove2me | Theorems.Thm_CosmoConstCentury_deceleration_parameter_and_cosmic_acceleration
-- name    : CosmoConstCentury.deceleration_parameter_and_cosmic_acceleration
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T14:47:15.222198+00:00
-- url     : https://prove2.me/theorems/01e1aa40-65bd-4ab9-9fef-f2b0134f4868
-- title:
--   Deceleration parameter $q=\tfrac12\Omega_M-\Omega_\Lambda$ (eq. 29); accelerated expansion requires $\Lambda>0$
-- statement:
--   Let $G>0$ and $c>0$, let $\Lambda$ be the cosmological constant and $k$ a real curvature index, and let $(R,\rho)$ solve the Friedmann–Lemaître dust equations on a set of times $I$. Let $t\in I$, and write $H=R'/R$, $q=-\frac{1}{H^2}\frac{R''}{R}$, $\Omega_M=\rho/\rho_c$ with $\rho_c=3H^2/(8\pi G)$, and $\Omega_\Lambda=\Lambda/(3H^2)$.
--
--   1. If $R'(t)\neq0$, then the deceleration parameter satisfies equation (29) of the review:
--   $$q=\frac12\,\Omega_M-\Omega_\Lambda .$$
--   2. If the expansion is accelerating at time $t$, $R''(t)>0$, and the matter density is non-negative, $\rho(t)\ge0$, then
--   $$\Lambda>0 .$$
--
--   The first part generalizes (28) to cosmologies with a cosmological constant; the second part is the reason why the observed acceleration of cosmic expansion (Sections 9–10) points to a positive cosmological constant.
--
--   **Formalization Note** The predicate `IsFriedmannSolution G c Λ k I R ρ` requires, at every $t\in I$, that $R(t)>0$, that $R$ is $C^2$ in a neighbourhood of $t$, and that the two equations hold with $\kappa=8\pi G/c^2$.
-- source:
--   C. O'Raifeartaigh, M. O'Keeffe, W. Nahm, S. Mitton, "One hundred years of the cosmological constant: from 'superfluous stunt' to dark energy", Eur. Phys. J. H 43, 73-117 (2018), https://doi.org/10.1140/epjh/e2017-80061-7; Section 7, pp. 92-93, eq. (29) (with eqs. (25)-(28)); density parameters Section 5.1 p. 85; accelerating expansion Sections 9.1 and 10.

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

theorem deceleration_parameter_and_cosmic_acceleration (G c Λ k : ℝ) (hG : 0 < G) (hc : 0 < c)
    (I : Set ℝ) (R ρ : ℝ → ℝ) (hsol : IsFriedmannSolution G c Λ k I R ρ) (t : ℝ) (ht : t ∈ I) :
    (deriv R t ≠ 0 → decelParam R t = omegaMatter G R ρ t / 2 - omegaLambda Λ R t) ∧
    (0 < deriv (deriv R) t → 0 ≤ ρ t → 0 < Λ) := by sorry

end CosmoConstCentury
