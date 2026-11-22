-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_simple_mark_compensated_process_L1_allactivity_20261122
-- name    : AvramDividend.Classical.avram_oai_original_physical_simple_mark_compensated_process_L1_allactivity_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:59:28.582629+00:00
-- url     : https://prove2.me/theorems/0d05260d-8d00-4be5-b000-b90e9127afce
-- title:
--   True original all-activity physical finite real simple signed compensated negative mark process has integrable first moments at every deterministic time
-- statement:
--   For any original spectrally negative Lévy process X (including infinite overall jump activity), locally finite-intensity measurable negative Borel mark region S, and arbitrary finite-range real SimpleFunc g, the ACTUAL physical signed centred mark-count process F_t=Σ_y y(N_(0,t](S∩{g=y})−tν(S∩{g=y})) is Integrable at every deterministic t. This applies independently Proved true original finite local negative Borel compensated mark-cell L1 integrability to each fibre and sums finitely. In combination with the already Proved source right-continuous StronglyAdapted F, conditional mean-zero of its mark increments, and real source marked count/compensator interval decomposition, this completes the integrability requirement of actual finite-simple mark martingality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_physical_simple_mark_compensated_process_L1_allactivity_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S)
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
        ((NX ω (Ioc 0 t ×ˢ B y)).toReal -
          (((t : ℝ≥0∞) * X.ν (B y))).toReal)) P := by sorry
