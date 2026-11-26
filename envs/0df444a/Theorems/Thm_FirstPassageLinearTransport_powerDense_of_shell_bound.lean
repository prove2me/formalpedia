-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_powerDense_of_shell_bound
-- name    : FirstPassageLinearTransport.powerDense_of_shell_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:57:32.722373+00:00
-- url     : https://prove2.me/theorems/54987a02-164d-4b81-b4bd-2aace2d5692f
-- title:
--   First Passage Linear Transport: power Dense of shell bound
-- statement:
--   Shell-to-global power-density transport.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L169-L276
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean#L169-L276

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.powerDense_of_shell_bound
    {S : Set ℕ} {K c : ℝ}
    (hK : 0 < K) (hc : 0 < c) (hclt : c < Real.log 2)
    (hshell : ∀ M : ℕ,
      ((shellBad S M).card : ℝ) ≤
        K * Real.exp (-c * M) * (2 : ℝ) ^ M) :
    PowerDense S
      (2 * K / (2 * Real.exp (-c) - 1))
      (c / Real.log 2) := by sorry
