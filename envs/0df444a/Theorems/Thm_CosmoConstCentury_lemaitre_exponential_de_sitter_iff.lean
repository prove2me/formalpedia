-- Prove2me | Theorems.Thm_CosmoConstCentury_lemaitre_exponential_de_sitter_iff
-- name    : CosmoConstCentury.lemaitre_exponential_de_sitter_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T09:21:31.466302+00:00
-- url     : https://prove2.me/theorems/446e057b-f0ee-4057-acbb-2c39c062050b
-- title:
--   Lemaître's exponential form of the de Sitter universe (eq. 14): $R=e^{at}$ with $\rho=0$, $k=0$ iff $\Lambda=3a^2$
-- statement:
--   Let $a$, $G$, $c$, $\Lambda$ be real constants. The empty ($\rho\equiv0$), spatially flat ($k=0$) universe with exponentially growing scale factor
--   $$R(t)=e^{at}$$
--   solves the Friedmann–Lemaître dust equations for all times if and only if
--   $$\Lambda=3a^2 .$$
--
--   This is the content of Lemaître's representation (14) of the de Sitter metric with a line element $e^{(\cdot)t}(-dx^2-dy^2-dz^2)+c^2dt^2$: the de Sitter universe is not static, but expands exponentially at a rate fixed by the cosmological constant.
--
--   **Formalization Note** The predicate `IsFriedmannSolution G c Λ k I R ρ` requires, at every $t\in I$, that $R(t)>0$, that $R$ is $C^2$ in a neighbourhood of $t$, and that the two equations hold with $\kappa=8\pi G/c^2$. The review writes the metric factor as $e^{a\sqrt\lambda\,t}$; here the scale factor itself is $e^{at}$ with a free rate $a$, and the theorem determines the relation between that rate and $\Lambda$.
-- source:
--   C. O'Raifeartaigh, M. O'Keeffe, W. Nahm, S. Mitton, "One hundred years of the cosmological constant: from 'superfluous stunt' to dark energy", Eur. Phys. J. H 43, 73-117 (2018), https://doi.org/10.1140/epjh/e2017-80061-7; Section 3.2, p. 81, eq. (14) (Lemaître 1925); equations (15)-(16) p. 82 with k = 0.

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

theorem lemaitre_exponential_de_sitter_iff (G c Λ a : ℝ) :
    IsFriedmannSolution G c Λ 0 Set.univ (fun t => Real.exp (a * t)) (fun _ => 0) ↔
      Λ = 3 * a ^ 2 := by sorry

end CosmoConstCentury
