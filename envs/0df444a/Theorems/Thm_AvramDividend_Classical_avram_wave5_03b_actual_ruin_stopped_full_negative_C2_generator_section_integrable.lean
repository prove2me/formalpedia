-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_section_integrable
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_section_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:03:34.986862+00:00
-- url     : https://prove2.me/theorems/314e2bd0-3838-4018-bd96-56cbe0090fc0
-- title:
--   Pointwise signed full negative Lévy generator jump section integrability at actual stopped prepayment reserve
-- statement:
--   For the original spectrally negative Lévy X, adapted dividend strategy D and localised general interior-C² test w, the actual inclusive-ruin-stopped nonlinear jump generator kernel, evaluated at the original prepayment reserve Y and integrated against X.nu restricted to all negative source marks, is pointwise integrable for every time and sample. Uses canonically Proved nonlinear Taylor section integrability and the exact negative-mark kernel equality, no independent Poisson source.
-- source:
--   Proved e336f7e2 actual generator/Taylor negative-mark equality, Proved 400350d3 actual C2 Taylor signed full-negative section integrability, pinned MeasureTheory.Integrable.congr and self_mem_ae_restrict.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_section_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_section_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∀ p : ℝ≥0 × Ω,
      Integrable (fun z : ℝ => JG (p,z))
        (X.ν.restrict (Iio (0 : ℝ))) := by sorry
