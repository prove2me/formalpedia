-- Prove2me | Theorems.Thm_FamousTheorems_norm_le_gronwallbound_of_norm_deriv_right_le
-- name    : FamousTheorems.norm_le_gronwallbound_of_norm_deriv_right_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:01.940775+00:00
-- url     : https://prove2.me/theorems/dccbeb7b-f8c9-4fed-9173-da59b01824f4
-- title:
--   Grönwall's inequality
-- statement:
--   **Grönwall's inequality.** If $\lVert f'(t)\rVert \le K\lVert f(t)\rVert + \varepsilon$ then $f$ is bounded by the solution of the corresponding linear equation, growing like $e^{Kt}$. A differential inequality is converted into an explicit bound on the function itself: knowing only how fast $f$ can change, one recovers how large it can become. This is the standard device for controlling error propagation. Applied to the difference of two solutions of an ODE it gives uniqueness and continuous dependence on initial conditions, with the $e^{Kt}$ factor quantifying how fast nearby trajectories can separate — which is precisely the bound that makes sensitive dependence in chaotic systems a statement about exponents rather than about unpredictability in principle. **Formalization note.** The hypothesis is on the right derivative, so the statement applies to functions differentiable only from one side. The result is Mathlib's `norm_le_gronwallBound_of_norm_deriv_right_le`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem norm_le_gronwallbound_of_norm_deriv_right_le :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
    [inst_1 : NormedSpace ℝ E] {f f' : ℝ → E} {δ K ε a b : ℝ}, 
    ContinuousOn f (Icc a b) → 
    (∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) → 
    ‖f a‖ ≤ δ → (∀ x ∈ Ico a b, ‖f' x‖ ≤ K * ‖f x‖ + ε) → ∀ x ∈ Icc a b, ‖f x‖ ≤ gronwallBound δ K ε (x - a) := by sorry

end FamousTheorems
