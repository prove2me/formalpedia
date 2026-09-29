-- Prove2me | Theorems.Thm_BlockCycleRotation_Q_eq_tripleSum
-- name    : BlockCycleRotation.Q_eq_tripleSum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:55:54.393606+00:00
-- url     : https://prove2.me/theorems/4cf0f3f4-8712-48f4-a0db-f9e182375459
-- title:
--   The quadruple sum as a triple sum over divisors, coprime pairs and $b\'$
-- statement:
--   For $n>0$ the sum of the $b$-components over the quadruples of $\mathcal{Q}(n)$ equals
--   $$\sum_{d \mid n} \; \sum_{(a,a',b') \in \mathcal{T}(n/d)} \left\lfloor \frac{n/d - a'b'}{a} \right\rfloor ,$$
--   the inner index set consisting of coprime pairs $a > a' \ge 1$ together with $b' \ge 1$ subject to $(a+a')b' < n/d$ and $n/d \equiv a'b' \pmod a$.
--
--   Eliminating the component $b$ in favour of a congruence condition is what turns the quadruple count into a sum an exponential-sum estimate can attack. This is the form on which §4 operates.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L214-L224

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.Q_eq_tripleSum {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesQ n, q.2.1
      = ∑ d ∈ n.divisors, ∑ t ∈ coprimeTriples (n / d), (n / d - t.2.1 * t.2.2) / t.1 := by sorry
