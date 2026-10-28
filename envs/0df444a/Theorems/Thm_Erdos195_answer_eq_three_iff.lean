-- Prove2me | Theorems.Thm_Erdos195_answer_eq_three_iff
-- name    : Erdos195.answer_eq_three_iff
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T13:32:24.444227+00:00
-- url     : https://prove2.me/theorems/14962be0-da3f-407d-9fc9-024a31f89af1
-- title:
--   Erdős #195 reduction: the answer is $3$ iff some permutation of $\mathbb{Z}$ avoids monotone $4$-APs
-- statement:
--   Let $K=\sup\{k\in\mathbb{N} : \text{every bijection } f:\mathbb{N}\to\mathbb{Z} \text{ has a monotone } k\text{-term AP}\}$, the quantity in the formal-conjectures statement of Erdős Problem 195. Then
--
--   $$K=3 \iff \exists f:\mathbb{N}\simeq\mathbb{Z} \text{ with no monotone } 4\text{-term AP}.$$
--
--   This connects the mission goal to the formal-conjectures answer variable; it follows from the bounds $3\le K\le 4$.
--
--   **Formalization Note** Permutations are `f : ℕ ≃ ℤ`; `HasMonotoneAP` is copied verbatim from formal-conjectures (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`): a list of indices `l` with `l.Pairwise (· < ·)` whose image is an arithmetic progression of length $k$, listed forwards or backwards.
-- source:
--   formal-conjectures ErdosProblems/195.lean (erdos_195, erdos_195.variants.leq_4_bound); Davis et al. 1977; Adenwalla arXiv:2211.04451 Theorem 1

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem answer_eq_three_iff :
    sSup {k : ℕ | ∀ f : ℕ ≃ ℤ, HasMonotoneAP f k} = 3 ↔ ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 4 := by sorry

end Erdos195
