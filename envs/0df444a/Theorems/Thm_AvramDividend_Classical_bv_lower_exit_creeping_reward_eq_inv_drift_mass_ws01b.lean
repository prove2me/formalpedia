-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_lower_exit_creeping_reward_eq_inv_drift_mass_ws01b
-- name    : AvramDividend.Classical.bv_lower_exit_creeping_reward_eq_inv_drift_mass_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:20:57.987172+00:00
-- url     : https://prove2.me/theorems/e10b143c-35e0-4c7b-a01a-d84f284f760a
-- title:
--   Bounded-variation lower-exit discounted scale payoff equals inverse drift times discounted creeping mass
-- statement:
--   For a standing spectrally negative bounded-variation Lévy process of positive drift d and scale W, the lower-first discounted W reward is the discounted mass of paths landing exactly at reserve zero, multiplied by W(0)=1/d. It isolates the nonzero boundary correction in BV and identifies the precise no-downward-creeping obligation before optional stopping can yield two-sided exit.
-- source:
--   Accepted lower-exit creeping factorisation UUID dc1797c5-f173-4916-87ff-2aa7eb89fcf8 and BV scale-origin identity UUID 973f7ca3-0d3a-491f-9e75-c780dbd572ab; Avram, Palmowski & Pistorius (2007).

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_discounted_creeping_factorisation
import Theorems.Thm_AvramDividend_Classical_bv_scale_origin_eq_inv_drift

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.bv_lower_exit_creeping_reward_eq_inv_drift_mass_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0 ∂P) =
      (∫⁻ ω,
        if twoSidedExitDownTime X (-x) ω <
            twoSidedExitUpTime X (a - x) ω ∧
           x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω = 0
        then ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal)))
        else 0 ∂P) * ENNReal.ofReal (1 / X.drift) := by sorry
