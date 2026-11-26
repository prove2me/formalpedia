-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_multiplicative_prefix_gt_of_crosses
-- name    : FirstPassageLinearTransport.exists_multiplicative_prefix_gt_of_crosses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:22:22.397572+00:00
-- url     : https://prove2.me/theorems/7f4c0802-d204-4455-b9d3-b627aeac1930
-- title:
--   First Passage Linear Transport: exists multiplicative prefix gt of crosses
-- statement:
--   A crossing of the recursive finite-word event is witnessed by an actual
--   prefix of the corresponding shortcut parity word.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L97-L128
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L97-L128

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.exists_multiplicative_prefix_gt_of_crosses :
    ∀ {r n : ℕ} {u z : ℝ},
      crossesMultiplicativeFrom u r z (boolParityWord r n) →
      ∃ H : ℕ, H ≤ r ∧
        u < z * ((3 : ℝ) ^ oddCount n H / (2 : ℝ) ^ H) := by sorry
