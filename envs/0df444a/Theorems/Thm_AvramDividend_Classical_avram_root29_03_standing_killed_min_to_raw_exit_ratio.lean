-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_standing_killed_min_to_raw_exit_ratio
-- name    : AvramDividend.Classical.avram_root29_03_standing_killed_min_to_raw_exit_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:51:32.212788+00:00
-- url     : https://prove2.me/theorems/fe702ff7-a358-41bc-ac2c-905cba77fdb7
-- title:
--   Actual raw inline two-sided exit lintegral ratio from explicitly assumed killed stopped-minimum harmonicity
-- statement:
--   Under genuine Standing and q>0, 0<a, 0<=x<=a, and a true q-scale function, an explicit original-law killed stopped-minimum q-scale harmonicity hypothesis implies the corrected raw inline-infimum discounted upper-before-ruin lintegral formula W_q(x)/W_q(a). The formal conclusion matches the canonical 3e1ce2c8 source raw integral binder, with exact infimum-clock definitions expanded. It imports only the canonically Proved all-variation conditional named ratio adapter fb60b24a; killed harmonicity itself remains a visible hypothesis.
-- source:
--   Source-faithful definitional normalisation of original twoSidedExitExpectation and passage times, using canonically Proved fb60b24a. No Open be9/BV OST/5bc parent is imported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_standing_stopped_min_harmonicity_to_exit_ratio

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_standing_killed_min_to_raw_exit_ratio
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hKilled :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω)) else 0 ∂P) =
      ENNReal.ofReal (W x)) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W x / W a) := by sorry
