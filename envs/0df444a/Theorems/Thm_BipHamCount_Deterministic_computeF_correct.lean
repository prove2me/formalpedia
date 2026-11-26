-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_computeF_correct
-- name    : BipHamCount.Deterministic.computeF_correct
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:23:38.375582+00:00
-- url     : https://prove2.me/theorems/44620cbe-1566-52d6-a54e-b638706d9f37
-- title:
--   Lemma 4.4: correctness of the executable small-term evaluator
-- statement:
--   Let $A,B$ be arbitrary integer matrices of order $m$, let $v$ be a left vertex and let $U,V$ be any vertex subsets. For every $0\leq k\leq m$, the small-term evaluator in Section 4 returns the integer $F(U,V)$ at threshold $k$, for every initial work counter. This certifies the full value computation in Lemma 4.4, including the construction of the polynomial matrix, its determinant and the signed coefficient sum.
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Lemma 4.4, p. 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Programs

namespace BipHamCount.Deterministic

/-- Functional correctness of the executable evaluator of Lemma 4.4. -/
theorem computeF_correct {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m)
    (k : ℕ) (hk : k ≤ m) (U V : Finset (Fin m)) (s : ℕ) :
    ((computeF m A B v k U V).run s).1 = Fval A B v k U V := by sorry

end BipHamCount.Deterministic
