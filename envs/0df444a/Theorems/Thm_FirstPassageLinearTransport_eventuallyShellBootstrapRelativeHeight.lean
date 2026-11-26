-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventuallyShellBootstrapRelativeHeight
-- name    : FirstPassageLinearTransport.eventuallyShellBootstrapRelativeHeight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:34:13.813048+00:00
-- url     : https://prove2.me/theorems/713c4d3c-13b1-58fe-99c0-f282ada136ed
-- title:
--   First Passage Linear Transport: eventually Shell Bootstrap Relative Height
-- statement:
--   On every sufficiently large shell, deleting the finite multiplicative
--   hit event gives a common shortcut/raw relative-height bound for the entire
--   fixed-barrier bootstrap chain.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L138-L213
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L138-L213

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventuallyShellBootstrapRelativeHeight
    {r eta omega : ℝ} (p : StageSetup r eta)
    (homega : 0 < omega) (hre : r * (1 + eta) ≤ 1) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ, ∀ H : ℝ,
      0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) →
      4 ≤ H → n ∉ shellMultiplicativeHit M (H / 4) →
      (∀ j : ℕ, j ≤ stageClock p (stageCount omega M) n →
        (orbit j n : ℝ) ≤ (n : ℝ) * H / 2) ∧
      (∀ i : ℕ, i ≤ rawTime n (stageClock p (stageCount omega M) n) →
        (rawOrbit i n : ℝ) ≤ (n : ℝ) * H) := by sorry
