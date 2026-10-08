-- Prove2me | Theorems.Thm_CosmoConstCentury_matter_only_deceleration
-- name    : CosmoConstCentury.matter_only_deceleration
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T12:04:44.211945+00:00
-- url     : https://prove2.me/theorems/81f8e172-9525-4c09-af04-b9b0b2340eb9
-- title:
--   Matter-only deceleration (eqs. 25–28): $R''/R=-\tfrac{4\pi G}{3}\rho$ and $q=\tfrac{4\pi G}{3H^2}\rho=\tfrac12\Omega_M$
-- statement:
--   Let $G>0$, $c>0$, let $k$ be a real curvature index, and let $(R,\rho)$ solve the Friedmann–Lemaître dust equations without cosmological constant ($\Lambda=0$) on a set of times $I$. Then at every $t\in I$:
--
--   1. the expansion decelerates according to (25),
--   $$\frac{R''}{R}=-\frac{4\pi G}{3}\rho;$$
--   2. if moreover $R'(t)\neq0$, the deceleration parameter $q=-\frac{1}{H^2}\frac{R''}{R}$ of (26) satisfies (27) and (28),
--   $$q=\frac{4\pi G}{3H^2}\rho=\frac12\,\Omega_M .$$
--
--   This is the basis, recalled in Section 7, of the 1950s programme to determine the density of matter from a measurement of the deceleration parameter $q_0$.
--
--   **Formalization Note** The predicate `IsFriedmannSolution G c Λ k I R ρ` requires, at every $t\in I$, that $R(t)>0$, that $R$ is $C^2$ in a neighbourhood of $t$, and that the two equations hold with $\kappa=8\pi G/c^2$.
-- source:
--   C. O'Raifeartaigh, M. O'Keeffe, W. Nahm, S. Mitton, "One hundred years of the cosmological constant: from 'superfluous stunt' to dark energy", Eur. Phys. J. H 43, 73-117 (2018), https://doi.org/10.1140/epjh/e2017-80061-7; Section 7, p. 92, eqs. (25), (26), (27), (28).

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

theorem matter_only_deceleration (G c k : ℝ) (hG : 0 < G) (hc : 0 < c) (I : Set ℝ)
    (R ρ : ℝ → ℝ) (hsol : IsFriedmannSolution G c 0 k I R ρ) (t : ℝ) (ht : t ∈ I) :
    deriv (deriv R) t / R t = -(4 * Real.pi * G / 3) * ρ t ∧
    (deriv R t ≠ 0 →
      decelParam R t = 4 * Real.pi * G / (3 * hubbleParam R t ^ 2) * ρ t ∧
      decelParam R t = omegaMatter G R ρ t / 2) := by sorry

end CosmoConstCentury
