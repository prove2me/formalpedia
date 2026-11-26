-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_heightCertifiedExceptionalCountEventually
-- name    : FirstPassageLinearTransport.heightCertifiedExceptionalCountEventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:13.828213+00:00
-- url     : https://prove2.me/theorems/9f4bf4a0-6e45-4035-af27-40726a42a118
-- title:
--   First Passage Linear Transport: height Certified Exceptional Count Eventually
-- statement:
--   The global exceptional count for the height-certified stretched-log set
--   retains the same stretched power of `log X`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L429-L473
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L429-L473

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.heightCertifiedExceptionalCountEventually
    {r eta chi Dc omega zeta alpha sigma : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega0 : 0 < omega)
    (hzeta : 0 < zeta)
    (halpha0 : 0 < alpha)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma ≤ 1)
    (hsigmaAlpha : sigma ≤ alpha)
    (hsigmaDensity : sigma < 1 - densityGamma omega chi) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      (badCount (assembledHeightCertified p omega zeta alpha) X : ℝ) ≤
        13 * X * Real.exp (-c * (Real.log X) ^ sigma) := by sorry
