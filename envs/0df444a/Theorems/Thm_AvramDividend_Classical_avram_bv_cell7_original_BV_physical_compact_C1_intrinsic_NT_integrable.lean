-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_physical_compact_C1_intrinsic_NT_integrable
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_physical_compact_C1_intrinsic_NT_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:09:28.100357+00:00
-- url     : https://prove2.me/theorems/7ac249c7-c00b-4548-9e61-dd251be47d9e
-- title:
--   Full original BV stopped physical C1 source integrable over the actual finite-horizon intrinsic jump measure
-- statement:
--   For the actual original BV spectrally negative Lévy process X and original admissible strategy D, the discounted compact-band C1 left-reserve negative-mark source is almost surely integrable against the same intrinsic original marked measure through every finite T. Both measurability and the all-negative-mark domination are discharged from separately proved original-process certificates, using original horizon/ruin truncation, zero exclusion and final contact. The theorem is the source-specific analytic half of the full original compensated H integrability bridge, whose pointwise equality with the physical source is already proved.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_intrinsic_weighted_negative_mark_mass_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_discounted_compact_C1_negative_mark_absolute_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_physical_compact_C1_intrinsic_NT_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q a b L R : ℝ) (hq : 0 ≤ q) (ha : 0 < a)
    (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0),
      let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      let E : Set (ℝ≥0 × ℝ) :=
        {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
      let K : ℝ≥0 × ℝ → ℝ := fun p =>
        if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
      let G : ℝ≥0 × ℝ → ℝ := fun p =>
        Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
      let Δ : ℝ≥0 → ℝ := fun v =>
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
      let NT : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict
          ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ Ioc 0 T)).map
            (fun v : ℝ≥0 => (v, Δ v)))
      Integrable G NT := by sorry
