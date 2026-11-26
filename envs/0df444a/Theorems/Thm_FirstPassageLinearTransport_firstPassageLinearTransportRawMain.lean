-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_firstPassageLinearTransportRawMain
-- name    : FirstPassageLinearTransport.firstPassageLinearTransportRawMain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:38:17.739907+00:00
-- url     : https://prove2.me/theorems/f907b699-0e1e-5992-b705-a2e807016f31
-- title:
--   First Passage Linear Transport: first Passage Linear Transport Raw Main
-- statement:
--   **Raw timed first-passage natural-density descent.** The literal raw
--   Collatz orbit reaches the same stretched-logarithmic target before
--   `10.44 log n` raw steps.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawNaturalDensityDescent.lean#L84-L136
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawNaturalDensityDescent.lean#L84-L136

import Definitions.Def_FirstPassageLinearTransport_RawClockBudget
import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.firstPassageLinearTransportRawMain
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ S : Set ℕ,
      NaturalDensityOne S ∧
        ∀ᶠ n : ℕ in atTop,
          n ∈ S →
            ∃ j : ℕ,
              (j : ℝ) < (261 / 25 : ℝ) * Real.log n ∧
                (rawOrbit j n : ℝ) ≤
                  Real.exp ((Real.log n) ^ (1 - delta)) := by sorry
