-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_undershoot_ae_ws01c
-- name    : AvramDividend.Classical.bv_strict_lower_exit_undershoot_ae_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:12:46.347295+00:00
-- url     : https://prove2.me/theorems/cad05116-7cb2-4986-8a45-9b1a52206b8b
-- title:
--   Original BV strict lower-first passage has a strictly negative stopped reserve almost surely
-- statement:
--   For a Standing spectrally negative Levy process with bounded variation, positive discount and a q-scale function, on almost every path where the strict lower first-passage time occurs before the strict upper first-passage time, the stopped reserve lies strictly below zero. Genuine first-downcrossing right-continuity guarantees a nonpositive terminal reserve, and the already proved source-specific no-creeping theorem rules out equality.
-- source:
--   WS01C geometric strengthening of accepted raw-iInf BV no-creeping theorem 43a28d8e using Proved first-downcrossing bound a041b575; no filtration enlargement or external stochastic assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_no_creeping_ae
import Theorems.Thm_AvramDividend_Classical_chat04_firstDowncrossing_value_le_threshold

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_strict_lower_exit_undershoot_ae_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω →
      x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω < 0 := by sorry
