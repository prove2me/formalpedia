-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_nonpositive_ae_positivepart_integrable_zero
-- name    : AvramDividend.Classical.avram_bv_residual9_nonpositive_ae_positivepart_integrable_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:52:29.585038+00:00
-- url     : https://prove2.me/theorems/e8f0cc12-6c7f-4444-9910-4e4a0968fd45
-- title:
--   A nonpositive original BV budget has integrable zero positive part without full signed integrability
-- statement:
--   A real random source that is nonpositive almost surely has an integrable identically-zero positive part and zero expected positive part, even when its negative tail is not integrable. This is the one-sided measure-theoretic bridge for original physical stopped B, preserving the distinction from full L1 integrability required by 4f851376.
-- source:
--   AVRAM BV-RESIDUAL9 round-three one-sided exact BV budget

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_nonpositive_ae_positivepart_integrable_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (f : Ω → ℝ) (hf : ∀ᵐ ω ∂P, f ω ≤ 0) :
    Integrable (fun ω => max (f ω) 0) P ∧
      (∫ ω, max (f ω) 0 ∂P) = 0 := by sorry
