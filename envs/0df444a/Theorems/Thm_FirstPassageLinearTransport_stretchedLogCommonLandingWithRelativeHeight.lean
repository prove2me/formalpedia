-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stretchedLogCommonLandingWithRelativeHeight
-- name    : FirstPassageLinearTransport.stretchedLogCommonLandingWithRelativeHeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:08.863679+00:00
-- url     : https://prove2.me/theorems/90702edd-ad01-4987-bcda-53ef1d21f26c
-- title:
--   First Passage Linear Transport: stretched Log Common Landing With Relative Height
-- statement:
--   Density-one stretched-logarithmic descent with one common shortcut/raw
--   landing and the smaller common relative-height allowance
--   `n * exp (zeta * (log n)^alpha)`.  This is the qualitative fixed-clock
--   specialization; the strict-exponent quantitative form follows below.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L699-L823
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L699-L823

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.stretchedLogCommonLandingWithRelativeHeight
    {delta zeta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hzeta : 0 < zeta) :
    ∃ S : Set ℕ,
      NaturalDensityOne S ∧
        ∀ᶠ n : ℕ in atTop,
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
                    (zeta * (Real.log n) ^ (1 - delta))) := by sorry
