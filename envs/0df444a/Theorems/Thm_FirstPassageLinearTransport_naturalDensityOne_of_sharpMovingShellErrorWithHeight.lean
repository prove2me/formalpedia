-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_naturalDensityOne_of_sharpMovingShellErrorWithHeight
-- name    : FirstPassageLinearTransport.naturalDensityOne_of_sharpMovingShellErrorWithHeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:56.425924+00:00
-- url     : https://prove2.me/theorems/cfc4aa9f-8a4d-5812-b221-59d7e0c69ff8
-- title:
--   First Passage Linear Transport: natural Density One of sharp Moving Shell Error With Height
-- statement:
--   A shell family satisfying the complete sharp Version 4 profile assembles
--   to a natural-density-one set when its relative-height allowance diverges.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L586-L600
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L586-L600

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.naturalDensityOne_of_sharpMovingShellErrorWithHeight
    (S : ℕ → Set ℕ) {A R : ℕ → ℝ} {C eps : ℝ}
    (heps : 0 < eps)
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hShell : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (S M) M ≤
        C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-eps))) + 4 / R M) :
    NaturalDensityOne (assembleDyadic S) := by sorry
