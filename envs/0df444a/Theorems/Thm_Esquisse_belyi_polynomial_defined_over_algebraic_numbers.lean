-- Prove2me | Theorems.Thm_Esquisse_belyi_polynomial_defined_over_algebraic_numbers
-- name    : Esquisse.belyi_polynomial_defined_over_algebraic_numbers
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T21:54:43.070488+00:00
-- url     : https://prove2.me/theorems/5d30c48e-ae4e-47d7-ae73-bca1e58c4820
-- title:
--   A Belyi polynomial over $\mathbb{C}$ is affinely equivalent to one with algebraic coefficients
-- statement:
--   Let $P \in \mathbb{C}[X]$ be a Belyi polynomial: $\deg P \ge 1$ and $P(z) \in \{0,1\}$ for every critical point $z \in \mathbb{C}$ (i.e. every $z$ with $P'(z) = 0$). Then there is an invertible affine substitution $X \mapsto aX + b$, $a \neq 0$, such that the polynomial $Q(X) = P(aX + b)$ has all of its coefficients algebraic over $\mathbb{Q}$.
--
--   This is the descent half of Grothendieck's observation in §3 of the Esquisse: a finite oriented map is realised not merely over $\mathbb{C}$ but over the algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$ inside $\mathbb{C}$, because the projective line and its three marked points $0, 1, \infty$ are already defined over the prime field. In the spherical (here: polynomial, i.e. clean tree) case, that assertion becomes the statement that the coefficients of the structural map may be taken to be algebraic numbers. The change of variable is necessary: it is the freedom in the source coordinate that has to be fixed before the coefficients can be recognised as algebraic.
-- source:
--   A. Grothendieck, Esquisse d'un Programme (1984), published in Geometric Galois Actions 1, LMS Lecture Note Series 242, CUP 1997, §3, pp. 15-16 of the French text: « comme la droite projective complexe est définie sur le corps de base absolu $\mathbb{Q}$, ainsi que les points de ramification admis, les courbes algébriques obtenues sont définies non seulement sur $\mathbb{C}$, mais sur la clôture algébrique $\overline{\mathbb{Q}}$ de $\mathbb{Q}$ dans $\mathbb{C}$ »; and p. 16, on the coefficients of $P$ and $Q$ being algebraic numbers.

import Mathlib
import Definitions.Def_esquisse_dessins_basic

open Polynomial

open Polynomial

namespace Esquisse

theorem belyi_polynomial_defined_over_algebraic_numbers (P : Polynomial ℂ)
    (hP : IsBelyiPolynomial P) :
    ∃ Q : Polynomial ℂ, AffineEquivalent P Q ∧ ∀ n : ℕ, IsAlgebraic ℚ (Q.coeff n) := by sorry

end Esquisse
