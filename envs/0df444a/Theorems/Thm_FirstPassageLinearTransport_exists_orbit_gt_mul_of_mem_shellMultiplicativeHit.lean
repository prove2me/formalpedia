-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_orbit_gt_mul_of_mem_shellMultiplicativeHit
-- name    : FirstPassageLinearTransport.exists_orbit_gt_mul_of_mem_shellMultiplicativeHit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:48.9358+00:00
-- url     : https://prove2.me/theorems/176b3b53-9d6b-5cbc-8fb3-b4929001a6c0
-- title:
--   First Passage Linear Transport: exists orbit gt mul of mem shell Multiplicative Hit
-- statement:
--   Membership in the shell multiplicative-hit event forces an actual
--   shortcut prefix above the corresponding relative-height ceiling.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L209-L228
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L209-L228

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.exists_orbit_gt_mul_of_mem_shellMultiplicativeHit
    {M n : ℕ} {u : ℝ} (hn : n ∈ shellMultiplicativeHit M u) :
    ∃ j : ℕ, j ≤ M ∧ u * (n : ℝ) < (orbit j n : ℝ) := by sorry
