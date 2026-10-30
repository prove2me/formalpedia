-- Prove2me | Theorems.Thm_ConsensusHalvingItems_Additive_loopStep_preserves
-- name    : ConsensusHalvingItems.Additive.loopStep_preserves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:38:32.519107+00:00
-- url     : https://prove2.me/theorems/8d29a662-f399-4be7-ace2-c3389e7a6f53
-- title:
--   Proof of Theorem 2.2: one iteration preserves a consensus halving
-- statement:
--   Let $x$ be a consensus halving for the additive utilities $u$, and let $T$ be any set of items. If one iteration of Step 3 from $(T, x)$ finds a solution $y \ne x$ of $S \cup T$ and produces the new point $s$ with
--
--   $$
--   s_j = (1 - \gamma_{j^*}) x_j + \gamma_{j^*} y_j ,
--   $$
--
--   then $s$ is again a consensus halving: $s$ satisfies equation (1), and $0 \le s_j \le 1$ for every item $j$. This is the step of the proof showing that $(x_1, \dots, x_m)$ remains a consensus halving throughout the algorithm.
--
--   Differences from the source:
--   - reading: real utilities ui(j) (no encoding fixed) → rational values u : Fin n → Fin m → ℚ; reason: an algorithm takes encoded input; reals have no finite encoding (Reading 2)
--   - encoding: the algorithm of Steps 1–4 with free choices (footnote 5's arbitrary non-pivot value, the argmin of Step 3b) → the definitions kernelDir / findSolution / loopStep / halve with the canonical kernel vector and lowest-index tie-break; reason: the paper leaves these choices open; any fixed choice is an instance of its algorithm (Reading 3)
--   - generalization: iterations of the algorithm (states reached from x ≡ 1/2, T = ∅) → any T and any consensus halving x; reason: the reached states satisfy the hypotheses; the statement specializes to the paper's
--   - generalization: nonnegative utilities; N = [n], M = [m] for positive n, m → values of any sign; n = 0 and m = 0 allowed; reason: the p. 6 remark extends the algorithm to negative values; the statement specializes to nonnegative values and positive n, m
--   - encoding: partition (M1, M2) of the items M = [m]; agents N = [n] → (x, 1 − x) with x : Fin m → ℚ; 0-based Fin n, Fin m; reason: a two-part partition is determined by its first part; same instances
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, ¶3, p. 5

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_loopStep
import Definitions.Def_ConsensusHalvingItems_Additive_IsConsensusHalving

namespace ConsensusHalvingItems.Additive

/-- **One iteration of Step 3 preserves a consensus halving.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, ¶3, p. 5: "Observe that, since both
(x1, . . . , xm) and (y1, . . . , ym) are solutions to the equations (1), their convex combination
(in Step 3c) also satisfies the equations (1). Furthermore, for each j such that yj ≠ xj, the
value γj is chosen so that if we replace γj∗ by γj in the formula for sj, we would have sj = 1 for
the case yj > xj, and sj = 0 for the case yj < xj. Since γj∗ ≤ γj, we have that sj ∈ [0, 1] for
all j such that yj ≠ xj. In addition, the value of xj does not change for j such that yj = xj."

If `x` is a consensus halving for `u`, then for every `T` and every start value `t` of the
counter, whenever one iteration `loopStep u T x` returns `some (T', x')`, the new point `x'` is
again a consensus halving for `u`.

**Formalization Note.** Partition `(x, 1 - x)`; the iteration is the paper's Step 3 with the
choices of Reading 3. No hypothesis on `T` is needed. -/
theorem loopStep_preserves {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) (t : ℕ) (T' : Finset (Fin m)) (x' : Fin m → ℚ)
    (hx : IsConsensusHalving u x) (hstep : ((loopStep u T x).run t).1 = some (T', x')) :
    IsConsensusHalving u x' := by sorry

end ConsensusHalvingItems.Additive
