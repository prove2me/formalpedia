-- Prove2me | Theorems.Thm_CosmoConstCentury_friedman_first_integral
-- name    : CosmoConstCentury.friedman_first_integral
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T09:46:00.155091+00:00
-- url     : https://prove2.me/theorems/22a361ca-76d2-45a0-8462-396c09c0601b
-- title:
--   Friedman's first integral (eq. 17) and conservation of $\kappa\rho R^3/3$
-- statement:
--   Let $c>0$, let $G$ and $\Lambda$ be real constants, and let $I\subseteq\mathbb R$ be an interval (a preconnected set of times). Let $(R,\rho)$ solve the closed ($k=1$) Friedmann–Lemaître dust equations (15)–(16) on $I$. Then there is a constant $A$ such that for every $t\in I$:
--
--   1. $\dfrac{\kappa\,\rho(t)\,R(t)^3}{3}=A$ (conservation of mass), and
--   2. Friedman's relation (17) holds:
--   $$\frac{1}{c^2}\Big(\frac{dR}{dt}\Big)^2=\frac{A-R+\frac{\Lambda}{3c^2}R^3}{R}.$$
--
--   Friedman used this integral to show that the magnitude of $\Lambda$ decides whether a matter-filled universe expands monotonically or expands and then contracts.
--
--   **Formalization Note** The predicate `IsFriedmannSolution G c Λ k I R ρ` requires, at every $t\in I$, that $R(t)>0$, that $R$ is $C^2$ in a neighbourhood of $t$, and that the two equations hold with $\kappa=8\pi G/c^2$.
-- source:
--   C. O'Raifeartaigh, M. O'Keeffe, W. Nahm, S. Mitton, "One hundred years of the cosmological constant: from 'superfluous stunt' to dark energy", Eur. Phys. J. H 43, 73-117 (2018), https://doi.org/10.1140/epjh/e2017-80061-7; Section 4, p. 82, eqs. (15), (16), (17) (Friedman 1922).

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

theorem friedman_first_integral (G c Λ : ℝ) (hc : 0 < c) (I : Set ℝ) (hI : IsPreconnected I)
    (R ρ : ℝ → ℝ) (hsol : IsFriedmannSolution G c Λ 1 I R ρ) :
    ∃ A : ℝ, ∀ t ∈ I, einsteinKappa G c * ρ t * R t ^ 3 / 3 = A ∧
      (1 / c ^ 2) * deriv R t ^ 2 = (A - R t + Λ * R t ^ 3 / (3 * c ^ 2)) / R t := by sorry

end CosmoConstCentury
