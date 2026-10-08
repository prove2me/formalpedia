-- Prove2me | Theorems.Thm_CosmoConstCentury_de_sitter_solution_B_iff
-- name    : CosmoConstCentury.de_sitter_solution_B_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T08:55:43.373244+00:00
-- url     : https://prove2.me/theorems/a59b0c0b-2619-47b1-8af4-ef72652e0f9e
-- title:
--   De Sitter's empty "Solution B" (eq. 13): $\rho=0$, $\Lambda=3c^2/R_0^2$
-- statement:
--   Let $R_0>0$ and let $G$, $c$, $\Lambda$ be real constants. Consider the empty universe ($\rho\equiv0$) with scale factor
--   $$R(t)=R_0\cosh\!\Big(\frac{ct}{R_0}\Big).$$
--   This pair solves the closed ($k=1$) Friedmann–Lemaître dust equations (15)–(16) for all times if and only if
--   $$\Lambda=\frac{3c^2}{R_0^2}.$$
--
--   In units with $c=1$ this is de Sitter's 1917 "Solution B", $\rho=0$, $\lambda=3/R^2$ (13), written in the closed slicing in which de Sitter space appears as a Friedmann universe of minimal radius $R_0$.
--
--   **Formalization Note** The predicate `IsFriedmannSolution G c Λ k I R ρ` requires, at every $t\in I$, that $R(t)>0$, that $R$ is $C^2$ in a neighbourhood of $t$, and that the two equations hold with $\kappa=8\pi G/c^2$. De Sitter's original static coordinates are not used; the cosh form is the representation of the same empty solution in the closed Friedmann slicing.
-- source:
--   C. O'Raifeartaigh, M. O'Keeffe, W. Nahm, S. Mitton, "One hundred years of the cosmological constant: from 'superfluous stunt' to dark energy", Eur. Phys. J. H 43, 73-117 (2018), https://doi.org/10.1140/epjh/e2017-80061-7; Section 3.2, p. 81, eqs. (12)-(13) (de Sitter 1917); equations (15)-(16) p. 82.

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

theorem de_sitter_solution_B_iff (G c Λ R₀ : ℝ) (hR₀ : 0 < R₀) :
    IsFriedmannSolution G c Λ 1 Set.univ (fun t => R₀ * Real.cosh (c * t / R₀)) (fun _ => 0) ↔
      Λ = 3 * c ^ 2 / R₀ ^ 2 := by sorry

end CosmoConstCentury
