-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_cap_extension_continuousOn_nonnegative
-- name    : AvramDividend.Classical.avram_p2_assist_p3_cap_extension_continuousOn_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:42:00.269999+00:00
-- url     : https://prove2.me/theorems/87e680b4-223d-431e-9db3-4d28705b752f
-- title:
--   Actual cap-linear extension inherits continuity on nonnegative reserves, including cap contact
-- statement:
--   For the actual finite or infinite cap continuation, source continuity on nonnegative reserves gives continuity of V on the same domain, including cap contact, because the linear branch is continuous and matches w at their frontier. This discharges the P3-F source-continuity premise when applying its actual physical C1 mesh grid to V.
-- source:
--   Pinned Mathlib ContinuousOn.if and frontier_Iic. True original cap-continuation equation, no globally C1 assumption at cap.

import Mathlib
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.DenselyOrdered
open Set
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p2_assist_p3_cap_extension_continuousOn_nonnegative
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (hw : ContinuousOn w (Ici (0 : ℝ))) :
    ContinuousOn V (Ici (0 : ℝ)) := by sorry
