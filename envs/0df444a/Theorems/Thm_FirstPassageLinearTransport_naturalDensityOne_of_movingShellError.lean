-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_naturalDensityOne_of_movingShellError
-- name    : FirstPassageLinearTransport.naturalDensityOne_of_movingShellError
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:24:50.576432+00:00
-- url     : https://prove2.me/theorems/4195798a-b9d6-4add-9eee-5fde6b21b279
-- title:
--   First Passage Linear Transport: natural Density One of moving Shell Error
-- statement:
--   A shell family with the moving endpoint error profile assembles to a
--   natural-density-one set.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L568-L582
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L568-L582

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.naturalDensityOne_of_movingShellError
    (S : ℕ → Set ℕ) {A : ℕ → ℝ} {C eps : ℝ}
    (heps : 0 < eps)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hShell : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (S M) M ≤
        C * ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-eps)))) :
    NaturalDensityOne (assembleDyadic S) := by sorry
