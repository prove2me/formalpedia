-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_Supplement_theorem_4_8
-- name    : AccelNewtonDinkelbach.Supplement.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:05:37.114525+00:00
-- url     : https://prove2.me/theorems/6def7148-47cf-45e5-964c-a2526a6bc7fe
-- title:
--   Theorem 4.8 — Algorithm 3 returns $y^{\max}$ when feasible and otherwise certifies infeasibility
-- statement:
--   Let $(G,c,\gamma)$ be an M2VPI system and $y^{\max}\in\bar{\mathbb R}^n$ its pointwise maximal solution, $y^{\max}_v=\sup\{y_v : y \text{ feasible}\}$. For every execution of Algorithm 3 (every node order, choice of flow-absorbing cycle in line 8, and Grapevine tie-break, hence every oracle answer):
--
--   1. if it returns labels $y$ and the M2VPI system is feasible, then $y=y^{\max}$;
--   2. if it returns `INFEASIBLE`, then the system is infeasible.
--
--   A label return is deliberately not claimed to imply feasibility.
--
--   Differences from the source:
--   - encoding: pseudocode with free choices → a relation Algorithm3Returns that holds for every execution allowed by lines 1–18, the Grapevine oracle and Algorithm 1; reason: preserves the nondeterminism rather than fixing one implementation
--   - reading: Grapevine continues to update ȳ throughout line 14 → both queries of an iteration warm-start from the current iterate's labels; failed look-ahead query labels are discarded and accepted-query labels are retained, with line 17 using the final accepted iterate; reason: this is the label state used in the proofs on pp.16–17
--   - encoding: y and y^max in R̄^n → EReal-valued labels and the coordinatewise supremum of feasible real labels; reason: represents the paper's +∞ coordinates
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Theorem 4.8, p.16

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_Supplement_Algorithm3

namespace AccelNewtonDinkelbach.Supplement

set_option autoImplicit false

/-- **Theorem 4.8 (correctness of Algorithm 3).**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Theorem 4.8, p.16.

For every execution of Algorithm 3 (every node order, choice of flow-absorbing cycle in line 8,
and Grapevine tie-break, hence every oracle answer): if it returns labels `y ∈ ℝ̄ⁿ` and the
system is feasible, then `y = ymax`; if it returns `INFEASIBLE`, the system is infeasible.

**Formalization Note** A label return alone is not asserted to imply feasibility (p.15: "this
does not necessarily imply that the full system (G, c, γ) is feasible"). `ymax` is the pointwise
supremum of feasible real solutions in `EReal`, so `+∞` coordinates are allowed. The execution
model is `M2VPI.Algorithm3Returns`; see its note for the label state inside line 14. -/
theorem theorem_4_8 {n m : ℕ} (M : M2VPI n m) (result : M2VPI.Algorithm3Result n)
    (hrun : M.Algorithm3Returns result) :
    (∀ y, result = .labels y → M.IsFeasible → y = M.ymax) ∧
      (result = .infeasible → ¬ M.IsFeasible) := by sorry

end AccelNewtonDinkelbach.Supplement
