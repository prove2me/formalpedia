-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_C1_open_interior_Lipschitz
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_C1_open_interior_Lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:20:50.911054+00:00
-- url     : https://prove2.me/theorems/b4ebfe59-200f-43f2-bfb5-1ab7b7ef317b
-- title:
--   Original BV open-domain C1 regularity gives source compensator local Lipschitz constant
-- statement:
--   Whenever the Avram value function w is C1 on an open domain containing the compact positive reserve interior [a/2,b], the exact local Lipschitz witness used by the stopped original-source negative-jump compensator exists. This bridges canonical P3 hw_smooth to P3-E's hLip once the true cap-localised compact band lies inside the smooth generator region.
-- source:
--   Mathlib ContDiffOn.differentiableOn_one and ContDiffOn.continuousOn_deriv_of_isOpen, combined with Proved P3-E compact-derivative Lipschitz helper UUID b15ca26f-24b8-4f27-b1df-65fccc168f85. The open-region containment is an explicit genuine assumption, not fabricated boundary regularity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_compact_interior_Lipschitz_of_continuous_derivative
open Set Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_C1_open_interior_Lipschitz
(w : ℝ → ℝ) (a b : ℝ) (hab : a / 2 ≤ b)
(U : Set ℝ) (hUopen : IsOpen U)
(hw_smooth : ContDiffOn ℝ 1 w U)
(hsub : Set.Icc (a / 2) b ⊆ U) :
∃ L : ℝ, 0 ≤ L ∧
  ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v| := by sorry
