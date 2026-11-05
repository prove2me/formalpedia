-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_negative_support_has_strict_cutoff
-- name    : AvramDividend.Classical.avram_p2_l_mesh_negative_support_has_strict_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:09:55.307526+00:00
-- url     : https://prove2.me/theorems/780463b2-7431-4576-976f-c3d7dfb555a9
-- title:
--   Negative topological support gives an explicit strict zero-test cutoff
-- statement:
--   Any real-valued function whose closed topological support lies wholly below zero admits a positive cutoff radius ρ such that f vanishes at every z>−ρ. The theorem turns the qualitative strictly-negative support condition of compact continuous marked tests into the quantitative support-cutoff input required by the original finite uniform-grid cadlag theorem. Its proof separates zero from the closed support by a metric ball and uses the globally negative support outside that ball; no compactness assumption is needed.

import Mathlib

open Set Topology

theorem AvramDividend.Classical.avram_p2_l_mesh_negative_support_has_strict_cutoff (f : ℝ → ℝ) (hneg : tsupport f ⊆ Iio (0 : ℝ)) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℝ, -ρ < z → f z = 0 := by sorry
