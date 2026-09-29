-- Prove2me | Theorems.Thm_BlockCycleRotation_Q_gt_tripleSum
-- name    : BlockCycleRotation.Q_gt_tripleSum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:46.783911+00:00
-- url     : https://prove2.me/theorems/eea615c4-c0cb-4d3d-97fd-d267db19fc75
-- title:
--   The paper's restricted triple sum
-- statement:
--   Let $\mathcal{Q}(n)$ be the set of quadruples $(a,b,a',b')$ with $a > a' \ge 1$, $b > b' \ge 1$ and $n = ab + a'b'$ — no coprimality is imposed. Restricting it by $b > a$, which breaks the symmetry between the two factorisations, and reindexing by $d = \gcd(a,a')$ gives
--   $$\sum_{\substack{(a,b,a',b') \in \mathcal{Q}(n) \\ a < b}} (a+b) = \sum_{d \mid n}\ \sum_{t \in \mathcal{T}^{>}(n/d,\,d)} \left( d\,a + \left\lfloor \frac{n/d - a'b'}{a} \right\rfloor \right).$$
--
--   The inner index set $\mathcal{T}^{>}(m,d)$ consists of triples $(a,a',b')$ with $a > a' \ge 1$ coprime, $b' \ge 1$, $(a+a')b' < m$, the congruence $m \equiv a'b' \pmod a$, and the bulk constraint $m - a'b' > d a^2$. Eliminating $b$ — determined by $n = ab + a'b'$ — is what turns the defining equation into that congruence.
--
--   This is the triple sum as the paper writes it. The constraint $m - a'b' > da^2$ separates a *bulk* range, where the inner sum over $b'$ is long enough for the arithmetic-progression estimate to beat the trivial bound, from a *small* range handled crudely; that split is what makes the error term $O(n^{3/2+\varepsilon})$ rather than $O(n^2)$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L747-L758

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.Q_gt_tripleSum {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1)
      = ∑ d ∈ n.divisors, ∑ t ∈ gtTriples (n / d) d,
          (d * t.1 + (n / d - t.2.1 * t.2.2) / t.1) := by sorry
