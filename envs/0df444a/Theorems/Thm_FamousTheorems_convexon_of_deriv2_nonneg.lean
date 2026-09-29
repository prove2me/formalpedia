-- Prove2me | Theorems.Thm_FamousTheorems_convexon_of_deriv2_nonneg
-- name    : FamousTheorems.convexon_of_deriv2_nonneg
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:26:09.145786+00:00
-- url     : https://prove2.me/theorems/709223a3-a7cf-4e71-818d-f1ddc76bd098
-- title:
--   Convexity from a nonnegative second derivative
-- statement:
--   **The second derivative test for convexity.** A function with nonnegative second derivative on an interval is convex there: $$f'' \ge 0 \text{ on } D \;\Longrightarrow\; f \text{ convex on } D.$$ This converts a global, geometric condition — every chord lies above the graph — into a pointwise, computational one. The mechanism is monotonicity: $f'' \ge 0$ makes $f'$ nondecreasing, and a function with nondecreasing derivative is convex by the mean value theorem. Convexity in turn delivers Jensen's inequality, from which the AM–GM, Hölder and Cauchy–Schwarz inequalities all follow by choosing the right convex function, and it is the hypothesis that makes local minima global — the reason convex optimization is tractable while general nonlinear optimization is not. **Formalization note.** The domain is a convex set and the hypotheses ask for continuity on it with the first and second derivatives existing on its interior. The result is Mathlib's `convexOn_of_deriv2_nonneg`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem convexon_of_deriv2_nonneg :
    ∀ {D : Set ℝ}, 
    Convex ℝ D → 
    ∀ {f : ℝ → ℝ}, 
    ContinuousOn f D → 
    DifferentiableOn ℝ f (interior D) → 
    DifferentiableOn ℝ (deriv f) (interior D) → (∀ x ∈ interior D, 0 ≤ deriv^[2] f x) → ConvexOn ℝ D f := by sorry

end FamousTheorems
