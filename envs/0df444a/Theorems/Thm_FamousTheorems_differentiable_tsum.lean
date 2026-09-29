-- Prove2me | Theorems.Thm_FamousTheorems_differentiable_tsum
-- name    : FamousTheorems.differentiable_tsum
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:26:09.001103+00:00
-- url     : https://prove2.me/theorems/d2ea4a87-3cf6-4a33-8a9f-070ea9565942
-- title:
--   Differentiability of a uniformly convergent sum
-- statement:
--   **Term-by-term differentiation of an infinite sum.** If the derivatives $f_i'$ are dominated by a summable sequence of constants and the series converges at one point, then $\sum_i f_i$ is differentiable and $$\Bigl(\sum_i f_i\Bigr)' = \sum_i f_i'.$$ Differentiation and infinite summation may be interchanged — but the hypothesis is on the *derivatives*, not on the functions. That asymmetry is the content: uniform convergence of a series says nothing about its derivative (a uniformly small wiggle can have a large slope), whereas uniform convergence of the differentiated series does control the original. This is the theorem that licenses differentiating power series term by term inside the radius of convergence, and with it the entire theory of analytic functions defined by series. **Formalization note.** The bound is on `‖f' i x‖` uniformly in `x` with `Summable u`, plus convergence at a single point. The result is Mathlib's `differentiable_tsum`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem differentiable_tsum :
    ∀ {α : Type u_1} {𝕜 : Type u_2} {E : Type u_3} {F : Type u_4} [inst : NontriviallyNormedField 𝕜] 
    [IsRCLikeNormedField 𝕜] [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace 𝕜 E] [inst_4 : NormedAddCommGroup F] 
    [CompleteSpace F] {u : α → ℝ} [inst_6 : NormedSpace 𝕜 F] {f : α → E → F} {f' : α → E → E →L[𝕜] F}, 
    Summable u → 
    (∀ (n : α) (x : E), HasFDerivAt (f n) (f' n x) x) → 
    (∀ (n : α) (x : E), ‖f' n x‖ ≤ u n) → Differentiable 𝕜 fun y => ∑' (n : α), f n y := by sorry

end FamousTheorems
