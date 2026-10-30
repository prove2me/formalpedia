-- Prove2me | Theorems.Thm_ConsensusHalvingItems_Additive_loopStep_freezes
-- name    : ConsensusHalvingItems.Additive.loopStep_freezes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:38:57.662847+00:00
-- url     : https://prove2.me/theorems/14cd992e-168a-48ef-bd8b-dfc43d234d56
-- title:
--   Proof of Theorem 2.2: each iteration freezes a new item at 0 or 1
-- statement:
--   Let $x$ be a consensus halving for the additive utilities $u$, and suppose one iteration of Step 3 from $(T, x)$ produces the state $(T', x')$. Then there is an item $j^* \notin T$ such that
--
--   1. $T' = T \cup \{j^*\}$;
--   2. $x'_{j^*} \in \{0, 1\}$;
--   3. $x'_j = x_j$ for every $j \in T$.
--
--   So each iteration freezes one new item at an uncut value, and frozen items never change. In particular the loop runs at most $m$ times.
--
--   **Formalization Note** The paper uses $j^* \notin T$ implicitly: the solution $y$ agrees with $x$ on $T$ while $y_{j^*} \ne x_{j^*}$.
--
--   Differences from the source:
--   - reading: real utilities ui(j) (no encoding fixed) → rational values u : Fin n → Fin m → ℚ; reason: an algorithm takes encoded input; reals have no finite encoding (Reading 2)
--   - encoding: the algorithm of Steps 1–4 with free choices (footnote 5's arbitrary non-pivot value, the argmin of Step 3b) → the definitions kernelDir / findSolution / loopStep / halve with the canonical kernel vector and lowest-index tie-break; reason: the paper leaves these choices open; any fixed choice is an instance of its algorithm (Reading 3)
--   - generalization: iterations of the algorithm (states reached from x ≡ 1/2, T = ∅) → any T and any consensus halving x; reason: the reached states satisfy the hypotheses; the statement specializes to the paper's
--   - generalization: nonnegative utilities; N = [n], M = [m] for positive n, m → values of any sign; n = 0 and m = 0 allowed; reason: the p. 6 remark extends the algorithm to negative values; the statement specializes to nonnegative values and positive n, m
--   - encoding: partition (M1, M2) of the items M = [m]; agents N = [n] → (x, 1 − x) with x : Fin m → ℚ; 0-based Fin n, Fin m; reason: a two-part partition is determined by its first part; same instances
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, ¶4, p. 5

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_loopStep
import Definitions.Def_ConsensusHalvingItems_Additive_IsConsensusHalving

namespace ConsensusHalvingItems.Additive

/-- **Step 3 freezes a new item at 0 or 1.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, ¶4, p. 5: "As noted above, our definition of γj
ensures that xj∗ ∈ {0, 1} after the execution of Step 3c. Furthermore, as the constraint
yj∗ = xj∗ is then immediately added to T, the value of xj∗ does not change for the rest of the
algorithm."

If `x` is a consensus halving for `u` and one iteration `loopStep u T x` returns
`some (T', x')`, then there is an item `j* ∉ T` with `T' = T ∪ {j*}` and `x' j* ∈ {0, 1}`,
and `x' j = x j` for every `j ∈ T`.

**Formalization Note.** `j* ∉ T` is used implicitly by the paper (the new solution agrees with
`x` on `T`, while `y_{j*} ≠ x_{j*}`); it bounds the number of iterations by `m`. -/
theorem loopStep_freezes {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) (t : ℕ) (T' : Finset (Fin m)) (x' : Fin m → ℚ)
    (hx : IsConsensusHalving u x) (hstep : ((loopStep u T x).run t).1 = some (T', x')) :
    ∃ js, js ∉ T ∧ T' = insert js T ∧ (x' js = 0 ∨ x' js = 1) ∧ ∀ j ∈ T, x' j = x j := by sorry

end ConsensusHalvingItems.Additive
