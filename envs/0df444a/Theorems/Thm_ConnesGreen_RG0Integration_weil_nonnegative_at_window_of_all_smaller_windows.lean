-- Prove2me | Theorems.Thm_ConnesGreen_RG0Integration_weil_nonnegative_at_window_of_all_smaller_windows
-- name    : ConnesGreen.RG0Integration.weil_nonnegative_at_window_of_all_smaller_windows
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T22:38:36.305119+00:00
-- url     : https://prove2.me/theorems/3e76ef61-e67d-47ab-9aa5-462aa45c17b9
-- title:
--   Original Weil positivity closes at a support boundary when every smaller window is positive
-- statement:
--   Let $c>0$. If the original Weil value of $g*\widetilde g$ is nonnegative for every admissible test in every positive window $t<c$, then it is nonnegative for every admissible test in the window $c$. The load-bearing compact-support lemma places each unchanged test inside a smaller positive window. Positivity at smaller windows is an explicit premise, not asserted globally. This is a conditional boundary reduction for the original Weil form; it is not RH or a separation result.
-- source:
--   monocap-tech/weil: WeilDefect/Connes/RG0DependencyIntegration.lean, original actor and metric adapters at 4ba3a3a569d72a0d5af2ba6ea320f948030dcca5; proof and statement boundaries recovered with Lean elaborator metadata.

import Theorems.Thm_ConnesGreen_supported_test_fits_smaller_window
import Definitions.Def_ConnesGreen_canonical_model
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

theorem ConnesGreen.RG0Integration.weil_nonnegative_at_window_of_all_smaller_windows (c : ℝ) (hc : 0 < c)
    (hsmall : ∀ t : ℝ, 0 < t → t < c → ∀ g : ℝ → ℂ, SupportedTest t g →
      0 ≤ (weilDistribution (conv g (starInv g))).re) :
    ∀ g : ℝ → ℂ, SupportedTest c g → 0 ≤ (weilDistribution (conv g (starInv g))).re := by sorry
