-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_proposition_4_1
-- name    : BipHamCount.Deterministic.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:48:49.401752+00:00
-- url     : https://prove2.me/theorems/eb53ae16-fad5-41df-99da-1decd99e5fb6
-- title:
--   Proposition 4.1 — large terms: exact output and entropy running time
-- statement:
--   Set $\alpha=60909/100000$ and $k=\lfloor\alpha m\rfloor$. There exist a constant $C>0$ and a natural exponent $c$, independent of all inputs, such that for every side size $m$, every pair of zero–one integer matrices $A,B$, and every left vertex $v$, the fixed largeTerms program, started at cost zero, returns $\sigma_{>k}$ and has cost
--   $$\operatorname{cost}(\mathrm{largeTerms})\le C(m+1)^c\exp\big(2m h(\alpha)\big).$$
--   Here $h$ is binary entropy in nats and $n=2m$. Correctness and cost are both conclusions; the program is not an existential input. This is the large-term component of the counting theorem.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and side sets → finite types with linear orders, with Fin m as the zero-based ordered side; reason: every finite ordered set admits this relabelling; the minor factors use identical increasing orders
--   - encoding: A and B are the zero–one adjacency matrices from §2 p.4 → integer matrices with explicit ZeroOne hypotheses; reason: these hypotheses specify exactly the source matrices and prevent entry bit lengths from being unconstrained
--   - reading: k=αn/2 with α=0.60909 used as an integer index → α=60909/100000 and kOf m=floor(60909m/100000), where n=2m; reason: an integer threshold is required by the valid-set DP; floor preserves the exponential bounds up to polynomial factors, including finitely many small m
--   - encoding: binary entropy H in base two → Real.binEntropy in nats with exp replacing 2 raised to H; reason: exp(m·binEntropy x)=2^(m·H(x)), including x=0,1
--   - encoding: O-star suppresses a factor polynomial in n → positive C and natural c, both chosen before every input, and the factor C(m+1)^c; reason: n=2m; this expresses the same polynomial-factor bound and includes small sizes
--   - reading: time of the algorithm in §4 → charged bit operations of the fixed program; integer arithmetic costs (size|a|+size|b|+1)², with charged subset, table, loop and buffer operations; reason: the counter is generic; the reused Work definition supplies no unit-cost arithmetic assumption here; this accounts conservatively for integers of polynomial bit length
--   - encoding: store permanent tables and then sum the large terms → store successive colex-addressed layers and accumulate each large summand when its layer is filled; reason: the recurrence, values, valid sets and counted operations are identical, and earlier layers are not needed after the next layer is complete
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), Proposition 4.1, p. 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Programs

open scoped BigOperators

namespace BipHamCount.Deterministic

/-- Proposition 4.1 pp.6–7: correctness AND bit-cost of the fixed large-term DP.
Constants are uniform over dimensions, matrices and the omitted vertex. -/
theorem proposition_4_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ,
      ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ), ZeroOne A → ZeroOne B →
        ∀ v : Fin m,
          ((largeTerms m A B v (kOf m)).run 0).1 = sigmaLarge A B v (kOf m) ∧
          (((largeTerms m A B v (kOf m)).run 0).2 : ℝ) ≤
            C * ((m : ℝ)+1)^c * Real.exp (2*m*Real.binEntropy alpha) := by sorry

end BipHamCount.Deterministic
