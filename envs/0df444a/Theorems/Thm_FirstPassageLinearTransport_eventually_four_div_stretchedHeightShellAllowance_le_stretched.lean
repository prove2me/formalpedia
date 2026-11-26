-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_four_div_stretchedHeightShellAllowance_le_stretched
-- name    : FirstPassageLinearTransport.eventually_four_div_stretchedHeightShellAllowance_le_stretched
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:09.094203+00:00
-- url     : https://prove2.me/theorems/b6be32cc-6f8d-4ec9-9f77-e9898d643a27
-- title:
--   First Passage Linear Transport: eventually four div stretched Height Shell Allowance le stretched
-- statement:
--   The reciprocal height cost has the same stretched-power shell form as
--   the fixed-barrier bootstrap error.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L303-L352
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L303-L352

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_four_div_stretchedHeightShellAllowance_le_stretched
    {zeta alpha sigma : ℝ} (hzeta : 0 < zeta)
    (halpha0 : 0 < alpha)
    (hsigmaAlpha : sigma ≤ alpha) :
    ∀ᶠ M : ℕ in atTop,
      4 / stretchedHeightShellAllowance zeta alpha M ≤
        4 * Real.exp
          (-(zeta * (Real.log 2 / 2) ^ alpha) *
            (QuantitativeDensity.stretchedShellScale M) ^ sigma) := by sorry
