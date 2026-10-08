-- Prove2me | Theorems.Thm_CosmoConstCentury_supercritical_universe_recollapses
-- name    : CosmoConstCentury.supercritical_universe_recollapses
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-05T11:10:30.275121+00:00
-- url     : https://prove2.me/theorems/0276ff02-6414-47a9-b53d-c7386b4473ee
-- title:
--   Without $\Lambda$, a universe denser than critical cannot expand forever
-- statement:
--   Let $G>0$, $c>0$, let $k$ be a real curvature index and $t_0$ a time. Let $R$, $\rho$ be functions such that at time $t_0$ the density exceeds the critical density,
--   $$\rho(t_0)>\rho_c\big(H(t_0)\big)=\frac{3H(t_0)^2}{8\pi G},\qquad H=R'/R .$$
--   Then $(R,\rho)$ is not a solution of the Friedmann–Lemaître dust equations with $\Lambda=0$ and curvature index $k$ on the whole future half-line $[t_0,\infty)$.
--
--   In other words, a supercritical universe without cosmological constant has a finite future: it cannot keep existing as a positive-radius solution for all later times, in line with the statement in Section 5.1 that such a cosmos would eventually collapse.
--
--   **Formalization Note** The predicate `IsFriedmannSolution G c Λ k I R ρ` requires, at every $t\in I$, that $R(t)>0$, that $R$ is $C^2$ in a neighbourhood of $t$, and that the two equations hold with $\kappa=8\pi G/c^2$.
-- source:
--   C. O'Raifeartaigh, M. O'Keeffe, W. Nahm, S. Mitton, "One hundred years of the cosmological constant: from 'superfluous stunt' to dark energy", Eur. Phys. J. H 43, 73-117 (2018), https://doi.org/10.1140/epjh/e2017-80061-7; Section 5.1, p. 85: with vanishing cosmological constant, a cosmos of density above critical is of spherical geometry and eventually collapses.

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

theorem supercritical_universe_recollapses (G c k t₀ : ℝ) (hG : 0 < G) (hc : 0 < c)
    (R ρ : ℝ → ℝ) (hsuper : criticalDensity G (hubbleParam R t₀) < ρ t₀) :
    ¬ IsFriedmannSolution G c 0 k (Set.Ici t₀) R ρ := by sorry

end CosmoConstCentury
