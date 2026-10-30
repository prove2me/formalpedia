-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_upper_endpoint_of_interior
-- name    : AvramDividend.Classical.avram_root29_03_upper_endpoint_of_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T07:58:20.135873+00:00
-- url     : https://prove2.me/theorems/01a564c9-226b-4dc4-a616-8eb1b4f54799
-- title:
--   Upper strict-exit scale ratio extends from the interior without upward regularity
-- statement:
--   For a Standing spectrally negative Levy process, positive q, scale function W and positive barrier a, suppose the genuine discounted strict upper-before-ruin scale-ratio identity holds at every interior reserve 0<y<a. Then the same identity at the upper endpoint x=a follows from initial-reserve monotonicity, the upper bound one and continuity of W at a. No positive-near-zero path regularity is assumed.
-- source:
--   This child isolates a genuine unresolved endpoint in the canonical 5bcf90e1 theorem. Its proof uses only already Proved  cd747fb7 monotonicity, dde72b60 expectation bound, positivity under Standing and the IsScaleFunction continuity axiom. The interior identity is an explicit hypothesis and no Open theorem is imported; this makes the reduction acyclic and useful to an independent interior-first Esscher/stochastic proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_monotone_initial_reserve
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_le_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_upper_endpoint_of_interior
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hInterior : ∀ y : ℝ, 0 < y → y < a →
      twoSidedExitExpectation X q a y = ENNReal.ofReal (W y / W a)) :
    twoSidedExitExpectation X q a a = ENNReal.ofReal (W a / W a) := by sorry
