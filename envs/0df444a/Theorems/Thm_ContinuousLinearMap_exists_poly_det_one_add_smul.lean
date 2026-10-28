-- Prove2me | Theorems.Thm_ContinuousLinearMap_exists_poly_det_one_add_smul
-- name    : ContinuousLinearMap.exists_poly_det_one_add_smul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:12.86935+00:00
-- url     : https://prove2.me/theorems/793230d8-ecd1-4d94-9415-c2c1bf3398cd
-- title:
--   `det (1 + t • T)` is a polynomial in `t` of degree at most the dimension
-- statement:
--   Let $T : \mathbb{R}^d \to \mathbb{R}^d$ be a linear map. Then there is a real polynomial
--   $p$ with $\deg p \le d$ such that
--
--   $$
--   \det\bigl(I + t\,T\bigr) \;=\; p(t) \qquad \text{for every } t \in \mathbb{R},
--   $$
--
--   where $I$ is the identity map.
--
--   The determinant of a one-parameter affine family of operators is therefore not merely smooth in
--   the parameter but *polynomial*, of degree bounded by the dimension. That is a much more rigid
--   statement, and it is what allows a quantity defined as an integral of such a determinant to be
--   pinned down on all of $\mathbb{R}$ by its values on an arbitrarily small interval.
--
--   **Formalization Note** $T$ is a continuous linear endomorphism of `EuclideanSpace ℝ (Fin d)`
--   and $\det$ is `ContinuousLinearMap.det`; the polynomial is produced as an element of
--   `Polynomial ℝ`, with the degree bound stated through `Polynomial.natDegree`.
-- source:
--   J. Milnor, Analytic proofs of the “hairy ball theorem” and the Brouwer fixed point theorem, Amer. Math. Monthly 85 (1978), 521–524, §1–§3; carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory
open Polynomial

theorem ContinuousLinearMap.exists_poly_det_one_add_smul {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∃ p : ℝ[X], p.natDegree ≤ d ∧ ∀ t : ℝ, (1 + t • T).det = p.eval t := by sorry
