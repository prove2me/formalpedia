-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_variable_negative_simplemark_interval_compensated_L1_allactivity_20261122
-- name    : AvramDividend.Classical.avram_oai_original_variable_negative_simplemark_interval_compensated_L1_allactivity_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:20:14.762152+00:00
-- url     : https://prove2.me/theorems/8a9b7715-9096-4cb8-940c-e6813cf9b512
-- title:
--   Original all-activity physical negative signed finite-simple mark compensated integral has L1 at every arbitrary time interval, without globally finite Lévy intensity
-- statement:
--   For the ACTUAL spectrally negative Lévy intrinsic marked-jump measure, any positive or zero-length time interval (s,t], any Borel negative mark region S with finite restricted ν(S) despite possibly infinite global negative jump activity, and any real signed finite-range simple mark g, the actual signed compensated marked count sum G_(s,t)=Σ_y y(NX((s,t]×(S∩g^-1{y})).toReal−(t−s)ν(S∩g^-1{y}).toReal) is Integrable under the physical probability measure. Derive directly from the previously Proved true all-activity original negative Borel marked count Campbell L1 theorem 181c4d7f, measurable finite-intensity mark fibres and pinned integrable_finset_sum. This is the exact reusable source-integrability lemma that discharges all signed simple mark per-cell L1 prerequisites in the original predictable finite-grid and stopped jump Ito–Meyer source without redoing fibre proof for each cell.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_variable_negative_simplemark_interval_compensated_L1_allactivity_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (hν : X.ν S < ⊤)
    (g : SimpleFunc ℝ ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    Integrable (fun ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc s t ×ˢ B y)).toReal -
          ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B y))).toReal)) P := by sorry
