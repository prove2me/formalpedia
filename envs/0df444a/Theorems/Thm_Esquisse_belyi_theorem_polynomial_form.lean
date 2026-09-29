-- Prove2me | Theorems.Thm_Esquisse_belyi_theorem_polynomial_form
-- name    : Esquisse.belyi_theorem_polynomial_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T21:53:47.107026+00:00
-- url     : https://prove2.me/theorems/aa7d32d3-2e51-4ebf-8a67-8eeffb1e9f39
-- title:
--   Belyi's theorem, polynomial form: any finite set of algebraic numbers can be mapped into $\{0,1\}$ by a Belyi polynomial over $\mathbb{Q}$
-- statement:
--   For every finite set $S \subseteq \overline{\mathbb{Q}}$ of algebraic numbers there exists a polynomial $f \in \mathbb{Q}[X]$ with rational coefficients such that
--
--   1. $f$ is a Belyi polynomial over $\overline{\mathbb{Q}}$: $\deg f \ge 1$ and every critical value of $f$ lies in $\{0,1\}$, i.e. $f(z) \in \{0,1\}$ whenever $f'(z) = 0$ for $z \in \overline{\mathbb{Q}}$; and
--   2. $f(\alpha) \in \{0,1\}$ for every $\alpha \in S$.
--
--   This is the polynomial (genus-zero, affine) form of Belyi's theorem, the statement that makes the dictionary between finite maps and curves over number fields effective: a map of the projective line to itself, defined over $\mathbb{Q}$, unramified outside $0$, $1$, $\infty$, that additionally swallows any prescribed finite set of algebraic numbers into $\{0,1\}$. The degree of $f$ is unconstrained. Note that no claim of minimality, uniqueness or effectivity is made, and the case $S = \varnothing$ merely asserts that some rational Belyi polynomial exists.
-- source:
--   G. V. Belyi, On Galois extensions of a maximal cyclotomic field, Izv. Akad. Nauk SSSR Ser. Mat. 43 (1979), 267-276 (main theorem; English translation Math. USSR-Izv. 14 (1980), 247-256). Cited in A. Grothendieck, Esquisse d'un Programme (1984), published in Geometric Galois Actions 1, LMS Lecture Note Series 242, CUP 1997, §3, p. 17 of the French text: « toute courbe algébrique définie sur un corps de nombres peut s'obtenir comme revêtement de la droite projective ramifié seulement en les points 0, 1, ∞ ».

import Mathlib
import Definitions.Def_esquisse_dessins_basic

open Polynomial

open Polynomial

namespace Esquisse

theorem belyi_theorem_polynomial_form (S : Finset AlgNum) :
    ∃ f : Polynomial ℚ, IsBelyiPolynomial (f.map (algebraMap ℚ AlgNum)) ∧
      ∀ α ∈ S, (f.map (algebraMap ℚ AlgNum)).eval α = 0
        ∨ (f.map (algebraMap ℚ AlgNum)).eval α = 1 := by sorry

end Esquisse
