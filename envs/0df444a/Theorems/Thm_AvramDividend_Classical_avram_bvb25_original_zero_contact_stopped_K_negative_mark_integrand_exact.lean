-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb25_original_zero_contact_stopped_K_negative_mark_integrand_exact
-- name    : AvramDividend.Classical.avram_bvb25_original_zero_contact_stopped_K_negative_mark_integrand_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:50:25.840182+00:00
-- url     : https://prove2.me/theorems/e6814efe-f399-4904-862b-69a7922f8bb6
-- title:
--   Original stopped finite-activity negative-mark K integrand at physical zero-contact no-source-jump clocks is exact discounted boundary loss
-- statement:
--   On an original physical no-negative-jump BV path where the actual controlled reserve is zero through the finite horizon, at every strictly positive original time inside the uniform clipped prefix, before or at the original ruin clock, and for every genuinely negative original Lévy mark, the complete original stopped K pointwise integrand, including every physical zero-and-cap guard and the actual prepayment left reserve, is exactly minus the true discount times the boundary candidate value. This is source-exact and uses the authoritative prepayment left-limit zero theorem; it is the missing marked-fibre simplification before integrating the original physical stopped negative-jump compensator.
-- source:
--   Accepted original zero-source prepayment leftLim lemma 810c78f4; exact H_n mark kernel in ed067740 and b0915396; source zero boundary value condition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_zero_contact_actual_predividend_leftLim_zero
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb25_original_zero_contact_stopped_K_negative_mark_integrand_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S)
    (hnb : (nhdsWithin t (Iio t)).NeBot)
    (hSource : ∀ s : ℝ≥0, s ≤ S →
      X.X s ω = (s : ℝ) * X.drift)
    (hZero : ∀ s : ℝ≥0, s ≤ S →
      riskProcess X x D s ω = 0)
    (w : ℝ → ℝ) (hw_neg : ∀ z < 0, w z = 0)
    (q T δ : ℝ) (z : ℝ)
    (htpos : 0 < t)
    (htPrefix : (t : ℝ) < T - δ)
    (htStop : (t : ℝ≥0∞) ≤ ruinTime X x D ω)
    (hz : z < 0) :
    (if 0 < t ∧ (t : ℝ) < T - δ ∧
        (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
        0 ≤ Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
        ENNReal.ofReal (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ C ∧ z < 0 then
      Real.exp (-(q * (t : ℝ))) *
        (w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) -
          w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))
      else 0) =
      -(Real.exp (-(q * (t : ℝ))) * w 0) := by sorry
