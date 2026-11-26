-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_initial_shortcut_raw_height_of_not_mem_shellMultiplicativeHit
-- name    : FirstPassageLinearTransport.initial_shortcut_raw_height_of_not_mem_shellMultiplicativeHit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:29:21.884299+00:00
-- url     : https://prove2.me/theorems/9f179fa8-4523-4de4-aadd-f875456fe1c0
-- title:
--   First Passage Linear Transport: initial shortcut raw height of not mem shell Multiplicative Hit
-- statement:
--   The exact first-block height interface used by the strengthened shell
--   theorem.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L351-L370
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L351-L370

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.initial_shortcut_raw_height_of_not_mem_shellMultiplicativeHit
    {M n : ℕ} {R : ℝ}
    (hn : n ∈ dyadicShell M)
    (hnGood : n ∉ shellMultiplicativeHit M (R / 4)) :
    (∀ j : ℕ, j ≤ M → (orbit j n : ℝ) < (n : ℝ) * R / 2) ∧
      (∀ i : ℕ, i ≤ rawTime n M →
        (rawOrbit i n : ℝ) ≤ (n : ℝ) * R) := by sorry
