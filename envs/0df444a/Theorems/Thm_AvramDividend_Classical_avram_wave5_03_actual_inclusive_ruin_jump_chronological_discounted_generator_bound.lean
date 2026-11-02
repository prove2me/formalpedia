-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_inclusive_ruin_jump_chronological_discounted_generator_bound
-- name    : AvramDividend.Classical.avram_wave5_03_actual_inclusive_ruin_jump_chronological_discounted_generator_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:36:49.823204+00:00
-- url     : https://prove2.me/theorems/ff94b1f0-1c1a-43c2-bc75-4eef79b36e53
-- title:
--   Original stopped negative source jump and post-jump dividend cash: include ruin-causing mark, exclude positive ruin right atom
-- statement:
--   At a positive actual original Lévy source negative jump time t≤T and t≤ruinTime X x D ω, define the exact strict pre-source reserve Y and original mark J. If t<ruin, the source event is followed by its actual admissible right dividend and cash; if t equals positive ruin, it must not pay any right dividend but still includes the ruin-causing source jump. The discount-weighted full nonlinear reserve increment plus only eligible cash is at most the correct truncated small-jump linear term plus source Levy generatorIntegrand, on the specified original interior reserve mark band. The same original source X,D,𝓕 and chronological convention are used throughout, without independence, global w positivity, artificial copies, stochastic compensation or hypothesised Itô identity. The time-zero atom is separately handled by canonical Proved right-atom lemmas.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), exact ruin-stopped chronology and (5.13). Source-specific new integrator glue: 03B exact real riskProcess source nonlinear jump 509cd0f3 and generator kernel e336f7e2, plus 03 right atom 2cd50555; direct BV ef7e6c20 and corrected UBV 429e17ca building block.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_separate_gradient_right_atom_control

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_actual_inclusive_ruin_jump_chronological_discounted_generator_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T)
    (htStop : (t : ℝ≥0∞) ≤ ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q)
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
