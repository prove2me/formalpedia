-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_HJB_generator_compact_bound_of_continuity
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_HJB_generator_compact_bound_of_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:39:41.806349+00:00
-- url     : https://prove2.me/theorems/fe1db065-b0bb-4ae8-b45b-93b1a9898318
-- title:
--   Finite compact bound for original continuous HJB generator residual
-- statement:
--   When the one-variable original HJB generator residual H is continuous on the true positive-reserve compact localisation band [a,b], there is a finite K≥0 dominating |H| throughout that band. This is the source analytic input to the original discounted HJB drift L1 helper; no global bound or assumed integrable drift is needed beyond this compact local continuity.
-- source:
--   Pinned Mathlib IsCompact.exists_isMaxOn and ContinuousOn.abs; analogous Proved P3-E continuous derivative compact-max proof b15ca26f.

import Mathlib
open Set Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_HJB_generator_compact_bound_of_continuity
(H : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
(hcont : ContinuousOn H (Set.Icc a b)) :
∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ Set.Icc a b, |H y| ≤ K := by sorry
