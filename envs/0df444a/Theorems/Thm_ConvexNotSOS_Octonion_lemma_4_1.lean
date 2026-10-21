-- Prove2me | Theorems.Thm_ConvexNotSOS_Octonion_lemma_4_1
-- name    : ConvexNotSOS.Octonion.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:47.356526+00:00
-- url     : https://prove2.me/theorems/a16df65f-0824-4b7b-9511-ae8659e8fd0d
-- title:
--   Lemma 4.1, first equality — trace formula for the octonionic quartic
-- statement:
--   Identify $(x,y)\in\mathbb O^k\times\mathbb O^k$ with its $16\times k$ real coordinate matrix $X$, and let $S_0,\ldots,S_8$ be the Clifford matrices from p. 9. Then
--
--   $$q^{\mathbb O}_k(X)=\tfrac12\operatorname{tr}(XX^\top)^2-\tfrac14\sum_{i=0}^{8}\operatorname{tr}(X^\top S_iX)^2.$$
--
--   This identity rewrites the octonion product expression in a form suitable for analyzing its matrix symmetries.
--
--   **Formalization Note.** This item states the first equality of Lemma 4.1. Its second equality, in terms of the projector onto the span of the $S_i$, is outside this item's scope.
-- source:
--   Saunderson, A convex form that is not a sum of squares, arXiv:2105.08432v2, p. 10, Lemma 4.1, first equality

import Definitions.Def_ConvexNotSOS_Octonion_Symmetry

namespace ConvexNotSOS.Octonion
open MvPolynomial

theorem lemma_4_1 (k : ℕ) (X : Matrix (Fin 16) (Fin k) ℝ) :
    evalM X (qPoly k) =
      (1 / 2 : ℝ) * (Matrix.trace (X * X.transpose)) ^ 2 -
      (1 / 4 : ℝ) * ∑ i : Fin 9,
        (Matrix.trace (X.transpose * S i * X)) ^ 2 := by sorry
end ConvexNotSOS.Octonion
