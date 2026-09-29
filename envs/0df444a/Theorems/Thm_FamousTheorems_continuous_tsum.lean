-- Prove2me | Theorems.Thm_FamousTheorems_continuous_tsum
-- name    : FamousTheorems.continuous_tsum
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:26:08.576683+00:00
-- url     : https://prove2.me/theorems/b1ff984e-ddb5-4a7c-a454-81a11f724329
-- title:
--   Continuity of a uniformly convergent sum
-- statement:
--   **Continuity of an infinite sum** under the Weierstrass $M$-test. If each term $f_i$ is continuous and $\lVert f_i(x)\rVert \le u_i$ with $\sum u_i$ summable, then $$x \mapsto \sum_i f_i(x)$$ is continuous. Summability of the dominating constants forces uniform convergence of the series, and the uniform limit of continuous functions is continuous. The $M$-test is the practical criterion: it replaces a statement about functions with a statement about a single numerical series, which is usually easy to check. This is how one establishes continuity of power series inside the radius of convergence, of Fourier series with absolutely summable coefficients, and of the Riemann zeta function on $\Re s > 1$ — where $|n^{-s}| = n^{-\sigma}$ gives the dominating series directly. **Formalization note.** The index type is arbitrary and `∑'` is the unconditional sum, so no ordering of the terms is needed; `Summable u` is the hypothesis on the bounds. The result is Mathlib's `continuous_tsum`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem continuous_tsum :
    ∀ {α : Type u_1} {β : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup F] [CompleteSpace F] 
    {u : α → ℝ} [inst_2 : TopologicalSpace β] {f : α → β → F}, 
    (∀ (i : α), Continuous (f i)) → 
    Summable u → (∀ (n : α) (x : β), ‖f n x‖ ≤ u n) → Continuous fun x => ∑' (n : α), f n x := by sorry

end FamousTheorems
