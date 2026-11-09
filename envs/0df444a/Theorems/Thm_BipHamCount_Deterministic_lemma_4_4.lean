-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_lemma_4_4
-- name    : BipHamCount.Deterministic.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:49:01.598196+00:00
-- url     : https://prove2.me/theorems/0dafd1fe-c5e0-494a-96a4-69e71c11b8b9
-- title:
--   Lemma 4.4 — F(X,Y): exact evaluation in polynomial bit cost
-- statement:
--   There exist a constant $C>0$ and a natural exponent $c$, independent of all data, such that for every side size $m$, zero–one integer matrices $A,B$, left vertex $v$, threshold $0\le k\le m$, and subsets $X,Y$ of the right side, the fixed computeF program returns $F(X,Y)$ and, when started at cost zero, satisfies
--   $$\operatorname{cost}(\mathrm{computeF})\le C(m+1)^c.$$
--   Correctness is part of the conclusion. The quantification includes empty $X,Y$, empty $Z=R\setminus(X\cup Y)$, and $|Z|<|\bar S|$ in the specification. This supplies the polynomial work per pair in the small-term algorithm; Berkowitz correctness and intermediate coefficient bit bounds remain obligations of its proof.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and side sets → finite types with linear orders, with Fin m as the zero-based ordered side; reason: every finite ordered set admits this relabelling; the minor factors use identical increasing orders
--   - encoding: A and B are the zero–one adjacency matrices from §2 p.4 → integer matrices with explicit ZeroOne hypotheses; reason: these hypotheses specify exactly the source matrices and prevent entry bit lengths from being unconstrained
--   - generalization: the fixed threshold k=αm → every natural threshold k (restricted to k≤m in the polynomial-cost statement); reason: the full source threshold kOf m is among these choices; no source instance is removed
--   - reading: time of the algorithm in §4 → charged bit operations of the fixed program; integer arithmetic costs (size|a|+size|b|+1)², with charged subset, table, loop and buffer operations; reason: the counter is generic; the reused Work definition supplies no unit-cost arithmetic assumption here; this accounts conservatively for integers of polynomial bit length
--   - encoding: polynomial time in n → positive universal C and natural c with cost at most C(m+1)^c, n=2m; reason: this is the same polynomial-time assertion, including all finite small sizes
--   - encoding: sum coefficients from q=0 through k → the program sums q=0 through min(k,m); reason: the statement assumes k≤m, so the endpoints coincide
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Lemma 4.4, p. 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Programs

open scoped BigOperators

namespace BipHamCount.Deterministic

/-- Lemma 4.4 pp.8–9, correctness and polynomial bit-cost for every X,Y.
The independent threshold 0≤k≤m includes kOf m and has no hidden input cost. -/
theorem lemma_4_4 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ,
      ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ), ZeroOne A → ZeroOne B →
        ∀ (v : Fin m) (k : ℕ), k ≤ m → ∀ X Y : Finset (Fin m),
          ((computeF m A B v k X Y).run 0).1 = Fval A B v k X Y ∧
          (((computeF m A B v k X Y).run 0).2 : ℝ) ≤ C * ((m : ℝ)+1)^c := by sorry

end BipHamCount.Deterministic
