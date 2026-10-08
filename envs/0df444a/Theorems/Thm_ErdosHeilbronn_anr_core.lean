-- Prove2me | Theorems.Thm_ErdosHeilbronn_anr_core
-- name    : ErdosHeilbronn.anr_core
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T07:05:29.024861+00:00
-- url     : https://prove2.me/theorems/0007bace-cb60-4679-b9b0-7e2861b5eb3d
-- title:
--   Alon–Nathanson–Ruzsa lemma (two variables, polynomial method)
-- statement:
--   Let F be a field with decidable equality, A and B finite nonempty subsets with |A| = k₁ + 1 and |B| = k₂ + 1, and let f be a nonzero polynomial in two variables of total degree at most k₁ + k₂. If the coefficient of x^k₁ y^k₂ in f·(x+y)^(k₁+k₂−deg f) is nonzero, then the set of sums a + b with a ∈ A, b ∈ B and f(a,b) ≠ 0 contains at least k₁ + k₂ − deg f + 1 elements. This is the engine behind the polynomial-method proof of the Erdős–Heilbronn restricted sumset theorem: it is proved by applying the Combinatorial Nullstellensatz to f·(x+y)^K ∏(x+y−c) over the value set C.
-- source:
--   N. Alon, M. B. Nathanson, I. Z. Ruzsa, The polynomial method and restricted sums of congruence classes, J. Number Theory 56 (1996)

import Mathlib

namespace ErdosHeilbronn

/-- The Alon-Nathanson-Ruzsa lemma, two variables: if `f ≠ 0` over a field `F` has
degree at most `k₁ + k₂`, `|A| = k₁ + 1`, `|B| = k₂ + 1`, and the coefficient of
`monomial (k₁, k₂)` in `f (x+y)^(k₁+k₂-deg f)` is nonzero, then the set of sums
`a + b` with `f(a,b) ≠ 0` has at least `k₁ + k₂ - deg f + 1` elements. -/
theorem anr_core {F : Type*} [Field F] [DecidableEq F]
    (A B : Finset F) (f : MvPolynomial (Fin 2) F) (hf : f ≠ 0)
    (k₁ k₂ : ℕ) (htA : k₁ + 1 = A.card) (htB : k₂ + 1 = B.card)
    (hdeg : MvPolynomial.totalDegree f ≤ k₁ + k₂)
    (hc : MvPolynomial.coeff (Finsupp.single 0 k₁ + Finsupp.single 1 k₂)
      (f * (MvPolynomial.X 0 + MvPolynomial.X 1) ^
        (k₁ + k₂ - MvPolynomial.totalDegree f)) ≠ 0) :
    (k₁ + k₂ - MvPolynomial.totalDegree f + 1)
      ≤ (((A.product B).filter (fun ab => MvPolynomial.eval ![ab.1, ab.2] f ≠ 0)).image
          (fun ab => ab.1 + ab.2)).card := by
  sorry

end ErdosHeilbronn
