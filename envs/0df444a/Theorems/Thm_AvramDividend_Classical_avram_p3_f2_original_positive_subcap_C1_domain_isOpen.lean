-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_positive_subcap_C1_domain_isOpen
-- name    : AvramDividend.Classical.avram_p3_f2_original_positive_subcap_C1_domain_isOpen
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:47:22.229193+00:00
-- url     : https://prove2.me/theorems/d0c42ed8-63bc-400b-9f5d-5b29bf1eab6f
-- title:
--   Original classical Lévy dividend strict positive subcap is an open Real domain
-- statement:
--   The source-exact strict positive reserve subcap 0<y and ENNReal.ofReal y<C is an open subset of the real line for every cap, including infinity. This discharges the hOpen prerequisite of the Proved original C1 uniform finite-mesh and commutator source estimates directly from their canonical ENNReal cap representation.

import Mathlib.Topology.Order.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_positive_subcap_C1_domain_isOpen (C : ℝ≥0∞) :
    IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by sorry
