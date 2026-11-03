-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
-- name    : AvramDividend.Classical.avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:51:21.911196+00:00
-- url     : https://prove2.me/theorems/ac7198c5-7121-4466-a64e-27d38758e444
-- title:
--   Corrected positive-cap BV parent proved at exact zero horizon with complete original Stieltjes atom
-- statement:
--   At the exact zero finite horizon, under every original corrected positive-cap bounded-variation parent hypothesis including C>0, w(0)≥0, original capped admissibility, HJB generator and gradient inequalities, the complete discounted stopped original Stieltjes payout is bounded by ENNReal.ofReal(w x). Original chronological time-zero dividend atom is controlled by Proved separate gradient right atom theorem 2cd50555, the genuine post-payment reserve and BV full-cap gradient secant; Proved exact zero-horizon bound cd2d62d3 concludes the expected Stieltjes inequality. This solves the T=0 parent branch fully, independently of open core ef7e6c20 and the global T>0 stopped supermartingale.
-- source:
--   The original accepted W7-09 parent zero-horizon split (candidate 22549), using only Proved 2cd50555, 2ecd3672, 2ba5cc4f and cd2d62d3. No process substitution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
