-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_heightCertifiedShellRatioLeStretched
-- name    : FirstPassageLinearTransport.eventually_heightCertifiedShellRatioLeStretched
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:57:08.66778+00:00
-- url     : https://prove2.me/theorems/72174c3a-0161-4948-9964-f3e5637d7275
-- title:
--   First Passage Linear Transport: eventually height Certified Shell Ratio Le Stretched
-- statement:
--   The height-certified shell retains the stretched-exponential bootstrap
--   rate.  The resulting rate is the minimum of the bootstrap rate and the
--   reciprocal height-allowance rate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L357-L425
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L357-L425

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_heightCertifiedShellRatioLeStretched
    {r eta chi Dc omega zeta alpha sigma : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega0 : 0 < omega)
    (hzeta : 0 < zeta)
    (halpha0 : 0 < alpha)
    (hsigma0 : 0 < sigma) (hsigmaAlpha : sigma ≤ alpha)
    (hsigmaDensity : sigma < 1 - densityGamma omega chi) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (heightCertifiedShell p omega zeta alpha M) M ≤
        6 * Real.exp
          (-c * (QuantitativeDensity.stretchedShellScale M) ^ sigma) := by sorry
