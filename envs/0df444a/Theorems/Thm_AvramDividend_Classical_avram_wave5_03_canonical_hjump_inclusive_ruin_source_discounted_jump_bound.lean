-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_canonical_hjump_inclusive_ruin_source_discounted_jump_bound
-- name    : AvramDividend.Classical.avram_wave5_03_canonical_hjump_inclusive_ruin_source_discounted_jump_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:47:04.70097+00:00
-- url     : https://prove2.me/theorems/44d89f97-1fce-4544-8b1d-cba640500cb0
-- title:
--   Canonical BV/UBV hjump exact original negative-source mark plus eligible dividend, including positive ruin, without positive-cap assumption
-- statement:
--   Under the identical `hjump` right-dividend hypothesis already stated in BOTH canonical BV and corrected UBV finite-horizon stochastic cores, and merely the source X dividend-strategy law, the actual strictly negative source Lévy jump plus its chronological right cash satisfies the exact discounted original-generator jump-kernel upper bound at positive times through the inclusive true ruin stopping clock. The source ruin-causing mark at time τ>0 is included, but no right dividend at τ>0 is allowed. No hC:0<C, nonnegative x, HJB generator inequality, smoothness or global w positivity is added; this removes the corrected UBV zero-cap compatibility gap without hypothesizing stochastic integration or compensation.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i); directly matches hJump of BV ef7e6c20 and corrected UBV 429e17ca and imports canonical 03B Proved 509cd0f3 and e336f7e2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Include a source negative mark at the genuine stopped ruin instant, but
exclude the inadmissible positive-ruin right payment. Before ruin, pay the
chronological right dividend after the original source jump. -/

theorem AvramDividend.Classical.avram_wave5_03_canonical_hjump_inclusive_ruin_source_discounted_jump_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (T t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T)
    (htStop : (t : ℝ≥0∞) ≤ ruinTime X x D ω)
    (q : ℝ)
    (u v ζ : ℝ) :
    let Y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let J : ℝ :=
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
    let W : ℝ :=
      if (t : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω
    let cash : ℝ :=
      if (t : ℝ≥0∞) < ruinTime X x D ω then
        rightLimit D t ω - D t ω else 0
    ∀ (hJneg : J < 0) (hBand : Y ∈ Icc (u + ζ) v),
    Real.exp (-(q * (t : ℝ))) *
      ((w W -
          w (Function.leftLim (fun s : ℝ≥0 =>
            riskProcess X x D s ω) t)) + cash) ≤
    Real.exp (-(q * (t : ℝ))) *
      ((if -1 < J then J * deriv w Y else 0) +
        SpectrallyNegativeLevy.generatorIntegrand w Y J) := by sorry
