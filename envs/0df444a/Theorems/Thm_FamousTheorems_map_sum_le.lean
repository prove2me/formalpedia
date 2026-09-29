-- Prove2me | Theorems.Thm_FamousTheorems_map_sum_le
-- name    : FamousTheorems.map_sum_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:13:12.579054+00:00
-- url     : https://prove2.me/theorems/9d2ae25c-ab7a-4aeb-85a6-8fdf805c91ef
-- title:
--   Jensen's inequality (finite sum form)
-- statement:
--   **Jensen's inequality.** For a convex $f$ and weights $w_i \ge 0$ summing to $1$, $$f\Bigl(\sum_i w_i x_i\Bigr) \le \sum_i w_i f(x_i).$$ A convex function of an average is at most the average of the values. Most classical inequalities are this one with a particular $f$: $-\log$ gives AM-GM, $x^p$ gives the power-mean inequalities, $e^x$ gives the Chernoff bound. The probabilistic form $f(\mathbb{E}X) \le \mathbb{E}f(X)$ is the same statement with weights read as a distribution, which is why variance is nonnegative and entropy is maximised by the uniform distribution. **Formalization note.** `ConvexOn` is convexity on a set and the points must lie in it. The result is Mathlib's `ConvexOn.map_sum_le`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem map_sum_le :
    ∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_3} {ι : Type u_4} [inst : Field 𝕜] 
    [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : AddCommGroup E] [inst_4 : AddCommGroup β] 
    [inst_5 : PartialOrder β] [IsOrderedAddMonoid β] [inst_7 : Module 𝕜 E] [inst_8 : Module 𝕜 β] 
    [IsStrictOrderedModule 𝕜 β] {s : Set E} {f : E → β} {t : Finset ι} {w : ι → 𝕜} {p : ι → E}, 
    ConvexOn 𝕜 s f → 
    (∀ i ∈ t, 0 ≤ w i) → ∑ i ∈ t, w i = 1 → (∀ i ∈ t, p i ∈ s) → f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i) := by sorry

end FamousTheorems
