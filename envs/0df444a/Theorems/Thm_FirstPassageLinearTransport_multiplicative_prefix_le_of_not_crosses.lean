-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_multiplicative_prefix_le_of_not_crosses
-- name    : FirstPassageLinearTransport.multiplicative_prefix_le_of_not_crosses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:45:14.864425+00:00
-- url     : https://prove2.me/theorems/c9568f52-e45a-4acf-b3db-d589ce0b3a70
-- title:
--   First Passage Linear Transport: multiplicative prefix le of not crosses
-- statement:
--   Avoiding the recursive multiplicative hit event bounds every pure
--   Collatz multiplicative prefix.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L47-L93
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L47-L93

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.multiplicative_prefix_le_of_not_crosses :
    ∀ {r n : ℕ} {u z : ℝ},
      0 ≤ z →
      ¬crossesMultiplicativeFrom u r z (boolParityWord r n) →
      ∀ H : ℕ, H ≤ r →
        z * ((3 : ℝ) ^ oddCount n H / (2 : ℝ) ^ H) ≤ u := by sorry
