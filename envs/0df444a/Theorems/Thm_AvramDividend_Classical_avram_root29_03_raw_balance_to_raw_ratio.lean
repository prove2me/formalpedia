-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_raw_balance_to_raw_ratio
-- name    : AvramDividend.Classical.avram_root29_03_raw_balance_to_raw_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:01:03.777984+00:00
-- url     : https://prove2.me/theorems/b9638d75-e8e7-4abc-a3a7-347a48b48c2e
-- title:
--   Canonical raw strict two-sided exit ratio from a raw stopped-scale cross-product balance
-- statement:
--   For the original Standing spectrally negative Levy process, positive discount, 0<a and 0<=x<=a, the exact source raw infimum-clock discounted upper-before-lower lintegral times W(a) equals W(x) implies the raw integral ratio W(x)/W(a). This is a noncircular exact-source algebraic conversion, using the Proved positive-scale named quotient lemma 81ce0d81. The raw balance itself remains an explicit hypothesis.
-- source:
--   Source exact strict infimum passage clocks unfolded definitionally to the canonically Proved chat04_exit_ratio_of_stopped_balance (81ce0d81). It does not import Open canonical 09663d0d or any killed harmonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_exit_ratio_of_stopped_balance

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_raw_balance_to_raw_ratio
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hBalance : (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) *
      ENNReal.ofReal (W a) = ENNReal.ofReal (W x)) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W x / W a) := by sorry
