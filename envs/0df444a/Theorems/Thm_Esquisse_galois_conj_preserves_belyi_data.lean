-- Prove2me | Theorems.Thm_Esquisse_galois_conj_preserves_belyi_data
-- name    : Esquisse.galois_conj_preserves_belyi_data
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T21:55:23.974086+00:00
-- url     : https://prove2.me/theorems/90f8e41d-8e39-480b-bae3-18ff755fb7d7
-- title:
--   The Galois action preserves Belyi polynomials, their degree, and all root multiplicities
-- statement:
--   Let $\gamma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and let $P \in \overline{\mathbb{Q}}[X]$ be a Belyi polynomial. Write $P^{\gamma}$ for the polynomial obtained by applying $\gamma$ to each coefficient of $P$. Then:
--
--   1. $P^{\gamma}$ is again a Belyi polynomial;
--   2. $\deg P^{\gamma} = \deg P$;
--   3. for all $c, z \in \overline{\mathbb{Q}}$, the multiplicity of $z$ as a root of $P - c$ equals the multiplicity of $\gamma(z)$ as a root of $P^{\gamma} - \gamma(c)$:
--   $$\mathrm{mult}_z(P - c) = \mathrm{mult}_{\gamma(z)}\big(P^{\gamma} - \gamma(c)\big).$$
--
--   Taking $c = 0$ and $c = 1$, clause 3 says that the vertices of the dessin above $0$ and above $1$ are permuted by $\gamma$ together with their orders: the degree and the two valency lists of a dessin are Galois invariants. In the words of the Esquisse, the orders of the vertices and faces of the map are the multiplicities of the zeros and poles of the rational function expressing its structural projection, and the Galois action is by conjugation of the coefficients.
-- source:
--   A. Grothendieck, Esquisse d'un Programme (1984), published in Geometric Galois Actions 1, LMS Lecture Note Series 242, CUP 1997, §3, pp. 15-16 of the French text: « les ordres des sommets et des faces ne sont autres que les multiplicités des zéros et des pôles de la fonction rationnelle (définie sur $\overline{\mathbb{Q}}$) sur $X$ »; and « l'opération d'un automorphisme $\gamma$ [...] est obtenue en appliquant $\gamma$ aux coefficients des polynômes $P$, $Q$ ».

import Mathlib
import Definitions.Def_esquisse_dessins_basic

open Polynomial

open Polynomial

namespace Esquisse

theorem galois_conj_preserves_belyi_data (γ : GaloisQ) (P : Polynomial AlgNum)
    (hP : IsBelyiPolynomial P) :
    IsBelyiPolynomial (galoisConj γ P) ∧ (galoisConj γ P).natDegree = P.natDegree ∧
      ∀ c z : AlgNum, (P - C c).rootMultiplicity z
        = (galoisConj γ P - C (γ c)).rootMultiplicity (γ z) := by sorry

end Esquisse
