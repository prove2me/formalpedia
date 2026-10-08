-- Prove2me | Theorems.Thm_CosmoConstCentury_critical_density_classification
-- name    : CosmoConstCentury.critical_density_classification
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T10:27:08.785274+00:00
-- url     : https://prove2.me/theorems/50abfc67-2744-4e50-bf61-33695f625330
-- title:
--   Critical density decides the spatial curvature when $\Lambda=0$
-- statement:
--   Let $G>0$, $c>0$, let $k$ be a real curvature index, and let $(R,\rho)$ solve the Friedmann–Lemaître dust equations with vanishing cosmological constant ($\Lambda=0$) and curvature index $k$ on a set of times $I$. At every $t\in I$, with $H=R'/R$ and the critical density $\rho_c=3H^2/(8\pi G)$:
--
--   1. $k>0$ (spherical geometry) if and only if $\rho>\rho_c$;
--   2. $k=0$ (Euclidean geometry) if and only if $\rho=\rho_c$;
--   3. $k<0$ (hyperbolic geometry) if and only if $\rho<\rho_c$.
--
--   This is the classification of cosmic models by the density parameter $\Omega=\rho/\rho_c$ described in Section 5.1, with the Einstein–de Sitter universe as the critical case.
--
--   **Formalization Note** The predicate `IsFriedmannSolution G c Λ k I R ρ` requires, at every $t\in I$, that $R(t)>0$, that $R$ is $C^2$ in a neighbourhood of $t$, and that the two equations hold with $\kappa=8\pi G/c^2$.
-- source:
--   C. O'Raifeartaigh, M. O'Keeffe, W. Nahm, S. Mitton, "One hundred years of the cosmological constant: from 'superfluous stunt' to dark energy", Eur. Phys. J. H 43, 73-117 (2018), https://doi.org/10.1140/epjh/e2017-80061-7; Section 5.1, p. 85, critical density rho_c = 3H0^2/8piG from eq. (18) and the classification that follows.

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

theorem critical_density_classification (G c k : ℝ) (hG : 0 < G) (hc : 0 < c) (I : Set ℝ)
    (R ρ : ℝ → ℝ) (hsol : IsFriedmannSolution G c 0 k I R ρ) (t : ℝ) (ht : t ∈ I) :
    (0 < k ↔ criticalDensity G (hubbleParam R t) < ρ t) ∧
    (k = 0 ↔ ρ t = criticalDensity G (hubbleParam R t)) ∧
    (k < 0 ↔ ρ t < criticalDensity G (hubbleParam R t)) := by sorry

end CosmoConstCentury
