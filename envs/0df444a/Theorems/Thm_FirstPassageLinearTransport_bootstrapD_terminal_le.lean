-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_bootstrapD_terminal_le
-- name    : FirstPassageLinearTransport.bootstrapD_terminal_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:34:57.423112+00:00
-- url     : https://prove2.me/theorems/fb076033-36ca-4fd3-b8c9-b99fb2f038d9
-- title:
--   First Passage Linear Transport: bootstrap D terminal le
-- statement:
--   Earlier density exponents dominate the terminal exponent.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L243-L249
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L243-L249

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.bootstrapD_terminal_le {chi Dc : ℝ} {j R : ℕ}
    (hchi0 : 0 ≤ chi) (hchi1 : chi ≤ 1) (hDc0 : 0 ≤ Dc)
    (hjR : j ≤ R) :
    bootstrapD chi Dc R ≤ bootstrapD chi Dc j := by sorry
