-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_local_Lipschitz_of_derivative_bound
-- name    : AvramDividend.Classical.avram_p3_e_compensator_local_Lipschitz_of_derivative_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:59:32.407607+00:00
-- url     : https://prove2.me/theorems/ef024510-5576-4e71-bbc1-a1acea5762ab
-- title:
--   Compact interior derivative bound supplies nonlinear jump local Lipschitz envelope
-- statement:
--   A bound |w'|≤L for w differentiable at each point of the closed interior interval [a/2,b] implies |w(u)-w(v)|≤L|u-v| for all u,v in the interval. The conclusion exactly discharges the local Lipschitz premise of the source-exact original BV compensated negative-jump and signed HJB theorems.
-- source:
--   Mathlib Convex.norm_image_sub_le_of_norm_deriv_le on convex_Icc, using only genuine differentiability and derivative bound. Independent of P3-F mesh limits and P3-G clocks; does not change canonical targets.

import Mathlib
open Set
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_local_Lipschitz_of_derivative_bound
(w : ℝ → ℝ) (a b L : ℝ)
(hdiff : ∀ y ∈ Set.Icc (a / 2) b, DifferentiableAt ℝ w y)
(hderiv : ∀ y ∈ Set.Icc (a / 2) b, |deriv w y| ≤ L) :
∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
  |w u - w v| ≤ L * |u - v| := by sorry
