-- Prove2me | Theorems.Thm_ErdosHeilbronn_anr_core_zmod
-- name    : ErdosHeilbronn.anr_core_zmod
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T08:11:04.48311+00:00
-- url     : https://prove2.me/theorems/e4f2789a-39ea-488b-9768-88472746c8ae
-- title:
--   Alon–Nathanson–Ruzsa lemma over ℤ/p (two variables, polynomial method)
-- statement:
--   Let p be prime, A and B finite subsets of ℤ/p with |A| = k₁ + 1 and |B| = k₂ + 1, and let f be a nonzero polynomial in two variables over ℤ/p of total degree at most k₁ + k₂. If the coefficient of x^k₁ y^k₂ in f·(x+y)^(k₁+k₂−deg f) is nonzero, then the set of sums a + b with a ∈ A, b ∈ B and f(a,b) ≠ 0 contains at least k₁ + k₂ − deg f + 1 elements. This is the engine of the polynomial-method proof of the Erdős–Heilbronn restricted sumset theorem; it follows from the Combinatorial Nullstellensatz applied to f·(x+y)^K ∏(x+y−c) over the value set.
-- source:
--   N. Alon, M. B. Nathanson, I. Z. Ruzsa, J. Number Theory 56 (1996)

import Mathlib

namespace ErdosHeilbronn

/-- The Alon-Nathanson-Ruzsa lemma, two variables, over ℤ/p: if `f ≠ 0` has degree
at most `k₁ + k₂`, `|A| = k₁ + 1`, `|B| = k₂ + 1`, and the coefficient of
`monomial (k₁, k₂)` in `f (x+y)^(k₁+k₂-deg f)` is nonzero, then the set of sums
`a + b` with `f(a,b) ≠ 0` has at least `k₁ + k₂ - deg f + 1` elements. -/
theorem anr_core_zmod {p : ℕ} (hp : p.Prime)
    (A B : Finset (ZMod p)) (f : MvPolynomial (Fin 2) (ZMod p)) (hf : f ≠ 0)
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
