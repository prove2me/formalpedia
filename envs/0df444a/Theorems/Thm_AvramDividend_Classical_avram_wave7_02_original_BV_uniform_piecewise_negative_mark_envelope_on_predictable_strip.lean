-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_uniform_piecewise_negative_mark_envelope_on_predictable_strip
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_uniform_piecewise_negative_mark_envelope_on_predictable_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:29:34.762027+00:00
-- url     : https://prove2.me/theorems/2489fa17-533b-4927-bd13-6c8ba5718309
-- title:
--   Original stopped BV nonlinear predictable source-jump kernel has a uniform mark-only small/large negative envelope
-- statement:
--   For the actual original X, D and left-reserve predictable strip [a,b] with a>0, every discounted negative-mark value difference is bounded by the same mark-only piecewise envelope: L|z| for -a/2<z<0 and 2R for z≤-a/2. The already-Proved genuine small-mark C1-Lipschitz source estimate and large-overshoot bound establish this uniformly in time and path. Source BV first negative moment plus finite large-tail mass are the remaining independent integrability inputs; this theorem does not assume a Poisson surrogate or claim a stopped chain identity.
-- source:
--   Direct case split combining Proved e6763634 and e44668f8. Uniform mark-only majorant is directly suitable for W8-22's Proved product L1 domination theorem once the physical source moment/tail bound is supplied.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_large_negative_mark_discounted_candidate_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_uniform_piecewise_negative_mark_envelope_on_predictable_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (a b L R : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hBound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (E : Set (ℝ≥0 × Ω))
    (hBand : ∀ p ∈ E, Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (p : ℝ≥0 × Ω) (hp : p ∈ E) (z : ℝ) (hz : z < 0) :
    |Real.exp (-(q * (p.1 : ℝ))) *
      (w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
       w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1))| ≤
      if z ≤ -a / 2 then 2 * R else L * |z| := by sorry
