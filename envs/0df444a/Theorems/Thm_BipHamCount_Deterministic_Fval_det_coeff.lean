-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_Fval_det_coeff
-- name    : BipHamCount.Deterministic.Fval_det_coeff
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:04:00.361947+00:00
-- url     : https://prove2.me/theorems/f0fb8fe2-91aa-5a5c-80cd-190702570a7d
-- title:
--   Lemma 4.4 determinant coefficient identity for F(X,Y)
-- statement:
--   Fix two arbitrary square integer matrices A,B of order m, a left vertex v, finite index sets U,V, and any natural threshold k. Form the constant matrix M by multiplying A and B using only intermediate indices outside U union V. Form Q(x) as the determinant after adding w_i(U,V) x to each diagonal entry except the one at v. Then F(U,V) equals the sum from q=0 to k of the coefficient of x^q in Q, with sign (-1)^(m-q+1). This is the algebraic identity in the proof of Lemma 4.4, prior to the implementation and bit-cost bounds.
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Lemma 4.4, p. 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Core

open scoped BigOperators Polynomial

namespace BipHamCount.Deterministic

/-- The determinant coefficient identity used in the proof of Lemma 4.4. -/
theorem Fval_det_coeff {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m)
    (k : ℕ) (U V : Finset (Fin m)) :
    let M : Matrix (Fin m) (Fin m) ℤ :=
      fun i j => ∑ z ∈ (U ∪ V)ᶜ, A i z * B z j
    let Q := (Matrix.diagonal (fun i => if i ≠ v then
      Polynomial.C (w A B U V i) * Polynomial.X else 0) + M.map Polynomial.C).det
    ∑ q ∈ Finset.range (k + 1), (-1 : ℤ) ^ (m - q + 1) * Q.coeff q =
      Fval A B v k U V := by sorry

end BipHamCount.Deterministic
