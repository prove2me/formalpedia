-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_berkowitz_det_correct
-- name    : BipHamCount.Deterministic.berkowitz_det_correct
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:20:35.102576+00:00
-- url     : https://prove2.me/theorems/1a3ebb4a-681a-4a30-9422-9ad807b9feab
-- title:
--   Correctness of the bit-charged integer and polynomial Berkowitz determinant programs
-- statement:
--   For a square array of integers, the division-free Berkowitz routine in the large-term algorithm returns the determinant of its input matrix. For an array of coefficient arrays representing polynomials in $\mathbb{Z}[x]$, the same routine with polynomial operations returns a coefficient array $q$ such that for every $k\ge0$,
--   $$q_k=[x^k]\det A(x).$$
--   Both identities hold in every order, including order zero, and for any initial work counter. Missing entries and coefficients are interpreted as zero. These are the correctness properties of the determinant computations in the large- and small-term algorithms of Section 4.
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Lemma 4.4, p. 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Arithmetic

open scoped BigOperators Polynomial

namespace BipHamCount.Deterministic

/-- Correctness of the two division-free determinant implementations used in Section 4. -/
theorem berkowitz_det_correct :
    (∀ (M : Array (Array ℤ)) (n s : ℕ),
      let A : Matrix (Fin n) (Fin n) ℤ :=
        fun i j => ((M[i.val]?.getD #[])[j.val]?).getD 0
      ((berkowitz intOps n M).run s).1 = A.det) ∧
    (∀ (M : Array (Array ZPoly)) (n s k : ℕ),
      let decode := fun a : ZPoly => ∑ t ∈ Finset.range a.size,
        Polynomial.monomial t (a[t]?.getD 0)
      let A : Matrix (Fin n) (Fin n) ℤ[X] :=
        fun i j => decode (((M[i.val]?.getD #[])[j.val]?).getD #[])
      ((((berkowitz polyOps n M).run s).1)[k]?).getD 0 = A.det.coeff k) := by sorry

end BipHamCount.Deterministic
