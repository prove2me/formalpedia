-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shiftedDensityScaleLower
-- name    : FirstPassageLinearTransport.shiftedDensityScaleLower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:28:42.256812+00:00
-- url     : https://prove2.me/theorems/9b59d853-5a87-567e-b66f-820587ed2461
-- title:
--   First Passage Linear Transport: shifted Density Scale Lower
-- statement:
--   A shifted shell scale dominates a fixed fraction of its unshifted
--   counterpart.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BootstrapSchedule.lean#L213-L229
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BootstrapSchedule.lean#L213-L229

import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section

theorem FirstPassageLinearTransport.shiftedDensityScaleLower (gamma : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    (1 / 5 : ℝ) * ((M : ℝ) + 4) ^ (1 - gamma) ≤
      (M : ℝ) * ((M : ℝ) + 4) ^ (-gamma) := by sorry
