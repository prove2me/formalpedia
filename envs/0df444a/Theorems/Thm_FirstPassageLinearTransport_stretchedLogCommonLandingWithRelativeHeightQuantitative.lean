-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stretchedLogCommonLandingWithRelativeHeightQuantitative
-- name    : FirstPassageLinearTransport.stretchedLogCommonLandingWithRelativeHeightQuantitative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:35:05.974469+00:00
-- url     : https://prove2.me/theorems/fb8f1e91-9fb8-4d9d-ad5c-865001ddd457
-- title:
--   First Passage Linear Transport: stretched Log Common Landing With Relative Height Quantitative
-- statement:
--   Quantitative common-landing stretched-logarithmic descent with the
--   smaller relative-height allowance.  Every strict exceptional exponent
--   `sigma < 1 - delta` is retained.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L828-L967
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L828-L967

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.stretchedLogCommonLandingWithRelativeHeightQuantitative
    {delta sigma zeta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hsigma0 : 0 < sigma) (hsigma : sigma < 1 - delta)
    (hzeta : 0 < zeta) :
    ∃ S : Set ℕ, ∃ c : ℝ,
      0 < c ∧
      (∀ᶠ X : ℕ in atTop,
        (badCount S X : ℝ) ≤
          13 * X * Real.exp (-c * (Real.log X) ^ sigma)) ∧
      (∀ᶠ n : ℕ in atTop,
        n ∈ S →
          ∃ k ell : ℕ,
            (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
            (ell : ℝ) < (261 / 25 : ℝ) * Real.log n ∧
            orbit k n = rawOrbit ell n ∧
            (orbit k n : ℝ) ≤
              Real.exp ((Real.log n) ^ (1 - delta)) ∧
            (∀ j : ℕ, j ≤ k →
              (orbit j n : ℝ) ≤
                (n : ℝ) * Real.exp
                  (zeta * (Real.log n) ^ (1 - delta))) ∧
            (∀ i : ℕ, i ≤ ell →
              (rawOrbit i n : ℝ) ≤
                (n : ℝ) * Real.exp
                  (zeta * (Real.log n) ^ (1 - delta)))) := by sorry
