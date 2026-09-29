-- Prove2me | Theorems.Thm_FamousTheorems_krasner_lemma
-- name    : FamousTheorems.krasner_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:21.624105+00:00
-- url     : https://prove2.me/theorems/c456870b-804b-4646-83eb-676bc4103d9e
-- title:
--   Krasner's lemma
-- statement:
--   **Krasner's lemma.** Let $K$ be a complete nontrivially normed field with an ultrametric absolute value, and $L$ an algebraic extension of $K$ carrying a norm that extends the one on $K$. Let $x\in L$ be separable over $K$ with all its conjugates in $L$, and let $y\in L$ be closer to $x$ than every other conjugate of $x$:
--   $$|x-y|<|x-x'|\quad\text{for every conjugate } x'\ne x.$$
--   Then $x\in K(y)$.
--
--   Krasner's lemma says that roots of polynomials over complete non-archimedean fields depend continuously on the coefficients in a strong sense. Nearby separable polynomials generate the same extensions. It is a basic tool in local field theory, used to show that local fields have finitely many extensions of each degree and to approximate local extensions by global ones.
--
--   **Formalization note.** Mathlib's `IsKrasner.krasner`, applied via the instance `IsKrasner.of_completeSpace`, which is Mathlib's proof of the classical lemma. The norm on `L` extends that of `K` through `NormedAlgebra K L`. `IsConjRoot K x x'` means $x$ and $x'$ have the same minimal polynomial over $K$, and `IntermediateField.adjoin K {y}` is $K(y)$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsKrasner.krasner`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem krasner_lemma {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
    [NormedAlgebra K L] [Algebra.IsAlgebraic K L] {x y : L} (hx : (minpoly K x).Separable)
    (sp : ((minpoly K x).map (algebraMap K L)).Splits) (hy : IsIntegral K y)
    (h : ∀ x' : L, IsConjRoot K x x' → x ≠ x' → ‖x - y‖ < ‖x - x'‖) :
    x ∈ IntermediateField.adjoin K {y} := by sorry

end FamousTheorems
