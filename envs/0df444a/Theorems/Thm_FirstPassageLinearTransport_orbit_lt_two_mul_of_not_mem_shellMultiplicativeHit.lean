-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_lt_two_mul_of_not_mem_shellMultiplicativeHit
-- name    : FirstPassageLinearTransport.orbit_lt_two_mul_of_not_mem_shellMultiplicativeHit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:45:33.548352+00:00
-- url     : https://prove2.me/theorems/66cb283b-24b8-538a-a997-ea0f8de4894b
-- title:
--   First Passage Linear Transport: orbit lt two mul of not mem shell Multiplicative Hit
-- statement:
--   Outside the finite-word hit event, every shortcut prefix up to the shell
--   rank is bounded by twice the prescribed multiplicative threshold.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L244-L274
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L244-L274

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.orbit_lt_two_mul_of_not_mem_shellMultiplicativeHit
    {M n : ℕ} {u : ℝ}
    (hn : n ∈ dyadicShell M) (hnGood : n ∉ shellMultiplicativeHit M u)
    {j : ℕ} (hj : j ≤ M) :
    (orbit j n : ℝ) < 2 * u * n := by sorry
