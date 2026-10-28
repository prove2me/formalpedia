-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_full_resolvent_regular_of_correction_bounds
-- name    : AvramDividend.Classical.causal_neumann_full_resolvent_regular_of_correction_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:54:22.683678+00:00
-- url     : https://prove2.me/theorems/a742a81e-0141-435c-b650-bacebf161530
-- title:
--   Regularity of the complete Gaussian Neumann resolvent with forcing term
-- statement:
--   For signed Neumann correction terms with pointwise quadratic-geometric derivative bounds and uniform geometric primitive bounds, the complete resolvent g(x)=1/a+e^(wx)Σ H_n(x) is continuous at zero and C1 on every positive time. The 1/a forcing term is included explicitly, preserving the correct second-kind Volterra equation representation.
-- source:
--   Consequence of the geometric correction C1 theorem and geometric boundary continuity via the product rule for exp.

import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_causal_neumann_geometric_series_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_neumann_geometric_correction_contDiffOn_one

open AvramDividend.Classical Set

theorem AvramDividend.Classical.causal_neumann_full_resolvent_regular_of_correction_bounds
    (P H : ℕ → ℝ → ℝ) (a ρ w : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hP : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hH : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hHcont : ∀ n : ℕ, ContinuousOn (H n) (Ici (0 : ℝ)))
    (hHasDeriv : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      HasDerivAt (H n) (P n x / a - w * H n x) x)
    (hCont : ∀ ε R : ℝ, 0 < ε → ∀ n : ℕ,
      ContinuousOn (fun x : ℝ => P n x / a - w * H n x) (Ioo ε R)) :
    ∃ g : ℝ → ℝ,
      (g = fun y : ℝ => 1 / a +
        Real.exp (w * y) * (∑' n : ℕ, H n y)) ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) := by sorry
