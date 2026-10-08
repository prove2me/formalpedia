-- Prove2me | Theorems.Thm_CosmoConstCentury_einstein_de_sitter_age
-- name    : CosmoConstCentury.einstein_de_sitter_age
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T11:40:38.654683+00:00
-- url     : https://prove2.me/theorems/cc9fee0b-f69b-45d8-8d0f-a000f8fbb2e2
-- title:
--   Einstein–de Sitter universe: the expansion age is $t=2/(3H)$
-- statement:
--   Let $G$ and $c$ be real constants and let $(R,\rho)$ solve the Friedmann–Lemaître dust equations with $\Lambda=0$ and flat space ($k=0$) for all times $t>0$ — the Einstein–de Sitter model, whose first equation is the review's (18), $(R'/R)^2=\kappa\rho c^2/3$. Assume that the universe is expanding, $R'(t)>0$ for all $t>0$, and that it starts from a big bang at $t=0$, i.e. $R(t)\to0$ as $t\to0^+$. Then for every $t>0$,
--   $$t=\frac{2}{3H(t)},\qquad H=R'/R .$$
--
--   This is the timespan of expansion of the Einstein–de Sitter model quoted in footnote 24 of the review, $t=2/(3H_0)$.
--
--   **Formalization Note** The predicate `IsFriedmannSolution G c Λ k I R ρ` requires, at every $t\in I$, that $R(t)>0$, that $R$ is $C^2$ in a neighbourhood of $t$, and that the two equations hold with $\kappa=8\pi G/c^2$.
-- source:
--   C. O'Raifeartaigh, M. O'Keeffe, W. Nahm, S. Mitton, "One hundred years of the cosmological constant: from 'superfluous stunt' to dark energy", Eur. Phys. J. H 43, 73-117 (2018), https://doi.org/10.1140/epjh/e2017-80061-7; Section 5.1, p. 85, eq. (18) (Einstein and de Sitter 1932) and footnote 24 (t = 2/(3H0), Einstein 1933).

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

theorem einstein_de_sitter_age (G c : ℝ) (R ρ : ℝ → ℝ)
    (hsol : IsFriedmannSolution G c 0 0 (Set.Ioi 0) R ρ)
    (hexp : ∀ t > 0, 0 < deriv R t) (hbang : Tendsto R (𝓝[>] 0) (𝓝 0)) :
    ∀ t > 0, t = 2 / (3 * hubbleParam R t) := by sorry

end CosmoConstCentury
