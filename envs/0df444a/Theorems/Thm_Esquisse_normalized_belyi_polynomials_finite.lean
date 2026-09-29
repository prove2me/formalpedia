-- Prove2me | Theorems.Thm_Esquisse_normalized_belyi_polynomials_finite
-- name    : Esquisse.normalized_belyi_polynomials_finite
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T21:56:11.46482+00:00
-- url     : https://prove2.me/theorems/b78227e1-f902-4941-b64a-2ec883ff4f0e
-- title:
--   Finitely many normalized Belyi polynomials of each degree
-- statement:
--   For every $n \in \mathbb{N}$, the set of polynomials $P \in \overline{\mathbb{Q}}[X]$ that are Belyi polynomials, monic, of degree exactly $n$, and normalized so that the coefficient of $X^{n-1}$ vanishes, is finite.
--
--   Monicity and the vanishing of the subleading coefficient are a normalization of the affine freedom $X \mapsto aX + b$: the translation $b$ is pinned by the second condition and the scaling $a$ by the first, up to a root of unity. The content of the statement is therefore the finiteness, for fixed $n$, of the set of clean genus-zero dessins with $n$ edges — the combinatorial rigidity that underlies both the descent to $\overline{\mathbb{Q}}$ and the finiteness of Galois orbits. Degenerate degrees are covered by the statement: for $n = 0$ the set is empty, since a Belyi polynomial is nonconstant, and for $n = 1$ it is the singleton $\{X\}$.
-- source:
--   A. Grothendieck, Esquisse d'un Programme (1984), published in Geometric Galois Actions 1, LMS Lecture Note Series 242, CUP 1997, §3, p. 16 of the French text: « quelles exactement sont les conjuguées de telle carte orientée donnée ? (il y en a, visiblement, un nombre fini seulement) » (finiteness of the set of maps of given degree, hence of any Galois orbit).

import Mathlib
import Definitions.Def_esquisse_dessins_basic

open Polynomial

open Polynomial

namespace Esquisse

theorem normalized_belyi_polynomials_finite (n : ℕ) :
    {P : Polynomial AlgNum |
      IsBelyiPolynomial P ∧ P.Monic ∧ P.natDegree = n ∧ P.coeff (n - 1) = 0}.Finite := by sorry

end Esquisse
