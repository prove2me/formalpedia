-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_finite_negative_band_NX_mark_integrable_ae_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_finite_negative_band_NX_mark_integrable_ae_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:12:19.016843+00:00
-- url     : https://prove2.me/theorems/4efa8579-471e-458a-829b-7bb65c0a5779
-- title:
--   Actual original physical finite negative mark source 246500be
-- statement:
--   Reuse already accepted original same-X finite negative physical marked-jump integral proof, with all private original mark and annulus lemmas replaced by the identical publicly proven shared declarations. Source is genuinely original signed mark; no finite total ν hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_finite_negative_band_facts
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_bounded_physical_rectangle_mark_integrable_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_finite_negative_band_NX_mark_integrable_ae_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∀ᵐ ω ∂P,
      NX ω (Ioc 0 T ×ˢ B) < ⊤ ∧
      IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
        (Ioc 0 T ×ˢ B) (NX ω) := by sorry
