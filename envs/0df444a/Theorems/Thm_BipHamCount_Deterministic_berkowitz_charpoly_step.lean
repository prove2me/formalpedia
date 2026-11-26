-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_berkowitz_charpoly_step
-- name    : BipHamCount.Deterministic.berkowitz_charpoly_step
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:12:14.713743+00:00
-- url     : https://prove2.me/theorems/1710b448-0d33-4e9d-82ad-2a1c8d510262
-- title:
--   Berkowitz Toeplitz recurrence for the characteristic coefficients of a bordered matrix
-- statement:
--   Let $R$ be a commutative ring and let $D$ be a square matrix indexed by a finite set. Adjoin a scalar $a$, a row $b$ and a column $c$ to form a bordered matrix $M$. Write $p_N(x)=\det(I-xN)$ and set $t_0=1$, $t_1=-a$, and $t_{l+2}=-bD^lc$ for $l\geq0$. For every $k\geq0$,
--   $$[x^k]p_M(x)=\sum_{j=0}^{k}t_{k-j}[x^j]p_D(x).$$
--   This gives the algebraic correctness of the Toeplitz update used by the division-free determinant procedure in Lemma 4.4.
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Lemma 4.4, p. 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
open scoped BigOperators

namespace BipHamCount.Deterministic

/-- The coefficient recurrence implemented by the Berkowitz Toeplitz step. -/
theorem berkowitz_charpoly_step {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (a : R) (b c : I → R) (D : Matrix I I R) (k : ℕ) :
    let t : ℕ → R
      | 0 => 1
      | 1 => -a
      | l+2 => -(∑ i, ∑ j, b i * (D^l) i j * c j)
    (Matrix.fromBlocks (fun _ _ : Unit => a) (fun _ i => b i) (fun i _ => c i) D).charpolyRev.coeff k =
      ∑ j ∈ Finset.range (k+1), t (k-j) * D.charpolyRev.coeff j := by sorry

end BipHamCount.Deterministic
