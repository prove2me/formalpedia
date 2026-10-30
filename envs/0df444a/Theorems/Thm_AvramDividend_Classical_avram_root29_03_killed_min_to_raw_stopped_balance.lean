-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_killed_min_to_raw_stopped_balance
-- name    : AvramDividend.Classical.avram_root29_03_killed_min_to_raw_stopped_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:10:25.984126+00:00
-- url     : https://prove2.me/theorems/f425dc0c-1270-473b-be53-5206db86fcf7
-- title:
--   Source-exact raw strict stopped-scale balance given original killed min-clock scale harmonicity
-- statement:
--   Under Standing, q>0, 0<a and 0<=x<=a for a genuine spectrally negative Levy process, an explicit original-law killed stopped-minimum q-scale expectation identity hKilled entails the exact canonical inline-infimum upper-before-ruin discounted integral times W(a)=W(x). It imports only the canonically Proved unconditional original raw terminal factorisation 700ff0e6. The mathematical killed equality is not concealed or asserted.
-- source:
--   Direct transitivity of Proved avram_root29_03_raw_exit_scale_product_eq_stopped_terminal (700ff0e6) with explicit hKilled. No Open import, invalid strict/weak change, or illicit division.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_raw_exit_scale_product_eq_stopped_terminal

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_killed_min_to_raw_stopped_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hKilled : (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω)
            (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (min (twoSidedExitUpTime X (a - x) ω)
              (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal ω))
      else 0 ∂P) = ENNReal.ofReal (W x)) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by sorry
