-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_prepayment_ruin_landing_and_overshoot_generator_jump_kernel_exact
-- name    : AvramDividend.Classical.avram_wave6_04_actual_prepayment_ruin_landing_and_overshoot_generator_jump_kernel_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T00:04:31.256415+00:00
-- url     : https://prove2.me/theorems/fd4177d1-9c5c-4436-8a20-b9f36fa239a3
-- title:
--   Actual prepayment generator at exact zero-landing atom and strict negative ruin overshoot with inclusive source ruin clock
-- statement:
--   For the controlled original Lévy prepayment left limit Y and exact original ruinTime (inclusive endpoint), an interior positive reserve with jump z=-Y lands at 0 and its generatorIntegrand retains w(0)-w(Y), plus +Y*w'(Y) exactly when Y<1. In strict overshoot z<-Y the negative extension w(y)=0 for y<0 replaces w(Y+z) by zero; the truncation correction is active precisely when -1<z. This protects any mass at z=-Y and the threshold z=-1 from accidental deletion, with no assumption w(0)=0.
-- source:
--   Original source SpectrallyNegativeLevy generatorIntegrand, original prepayment rightLimit D leftLimit controlled reserve, inclusive ruinTime; endpoint guard for C2 Itô–Meyer compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_prepayment_ruin_landing_and_overshoot_generator_jump_kernel_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ)
    (p : ℝ≥0 × Ω) :
    let Y : ℝ≥0 × Ω → ℝ := fun r => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
    Y p ∈ Icc (u + δ) v →
    let R : ℝ :=
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    (R * SpectrallyNegativeLevy.generatorIntegrand w (Y p) (-(Y p)) =
      R * (w 0 - w (Y p) +
        if Y p < 1 then Y p * deriv w (Y p) else 0)) ∧
    (∀ z : ℝ, z < -(Y p) →
      R * SpectrallyNegativeLevy.generatorIntegrand w (Y p) z =
        R * (-w (Y p) -
          if -1 < z then z * deriv w (Y p) else 0)) := by sorry
