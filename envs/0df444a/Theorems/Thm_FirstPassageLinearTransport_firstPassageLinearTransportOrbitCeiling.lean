-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_firstPassageLinearTransportOrbitCeiling
-- name    : FirstPassageLinearTransport.firstPassageLinearTransportOrbitCeiling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:24.303923+00:00
-- url     : https://prove2.me/theorems/c83e0795-a4a9-55dc-97f2-9fbe71c3227a
-- title:
--   First Passage Linear Transport: first Passage Linear Transport Orbit Ceiling
-- statement:
--   One density-one set and one witness simultaneously satisfy the shortcut
--   clock, the stretched-log landing, and the intermediate-orbit ceiling through
--   that witness.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L591-L665
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L591-L665

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.firstPassageLinearTransportOrbitCeiling
    {delta beta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) (hbeta : 0 < beta) :
    ∃ S : Set ℕ,
      NaturalDensityOne S ∧
        ∀ᶠ n : ℕ in atTop,
          n ∈ S →
            ∃ k : ℕ,
              (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
                (orbit k n : ℝ) ≤
                  Real.exp ((Real.log n) ^ (1 - delta)) ∧
                ∀ j : ℕ, j ≤ k →
                  (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by sorry
