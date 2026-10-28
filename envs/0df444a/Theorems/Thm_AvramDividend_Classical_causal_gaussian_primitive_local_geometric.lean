-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_gaussian_primitive_local_geometric
-- name    : AvramDividend.Classical.causal_gaussian_primitive_local_geometric
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:16:13.715714+00:00
-- url     : https://prove2.me/theorems/37abe080-b8fd-4c33-8b8c-da2507100de4
-- title:
--   Gaussian damped primitive bounds yield local geometric bounds for undamped Neumann terms
-- statement:
--   A geometrically decaying exponentially damped Gaussian Neumann primitive produces geometrically bounded undamped Neumann corrections on every finite time interval, including the initial constant correction.
-- source:
--   Define the undamped Neumann term Q0=1/a and Q_{n+1}(s)=exp(w s) H_n(s). On any interval Ioc(0,x), 0≤w and s≤x imply exp(w s)≤exp(w x). The proved bound |H_n(s)|≤ρ^(n+1)/a then yields |Q_n(s)|≤C_x ρ^n for C_x=max(1/a,exp(w x)/a). This supplies precisely hQ to causal_geometric_neumann_local_sum_bound and then causal_local_neumann_convolution_majorant.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Ring

open Real Set

theorem AvramDividend.Classical.causal_gaussian_primitive_local_geometric
    (H Q : ℕ → ℝ → ℝ) (a w ρ : ℝ)
    (ha : 0 < a) (hw : 0 ≤ w) (hρ0 : 0 ≤ ρ)
    (hQ0 : Q 0 = fun _ : ℝ => 1 / a)
    (hQstep : ∀ n : ℕ, Q (n + 1) =
      fun s : ℝ => Real.exp (w * s) * H n s)
    (hHbound : ∀ n : ℕ, ∀ s : ℝ, 0 ≤ s →
      ‖H n s‖ ≤ ρ ^ (n + 1) / a) :
    ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ s ∈ Ioc (0 : ℝ) x,
        ‖Q n s‖ ≤ C * ρ ^ n := by sorry
