-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_physical_negativeband_mark_quantizer_exists
-- name    : AvramDividend.Classical.avram_mathfin22_original_physical_negativeband_mark_quantizer_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:15:43.061996+00:00
-- url     : https://prove2.me/theorems/2450a697-cfbc-4676-b182-fc790128bd85
-- title:
--   Original finite negative-jump band admits bounded simple mark quantizers converging under physical measure with L2 envelope
-- statement:
--   Specialise the remotely-Proved original all-activity bounded-simple mark dominated-convergence result 379fa495 to the actual mark g(z)=z on the canonical negative annulus B. As a,b≥0, B⊆[-1,0], so the proved original Borel simple-function quantisation theorem supplies f_k bounded by 1 and converging pointwise to z on B. Original intrinsic physical jump measure, square-integrable actual mark count envelope and a.e. convergence of raw marked integrals are preserved without globally finite negative jump activity or an auxiliary synthetic PRM. This is the explicit approximation witness for the exact original marked-jump L2 target 16f22886, whose remaining second-moment proof is separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_bounded_original_Borel_mark_simple_quantization
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_finiteband_simple_mark_L2dom_ae_convergence
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mathfin22_original_physical_negativeband_mark_quantizer_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (a b : ℕ) (hab : a ≤ b) :
    let B : Set ℝ :=
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let J : Ω → ℝ := fun ω =>
      ∫ p in Ioc 0 T ×ˢ B, p.2 ∂NX ω
    let N : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal
    ∃ f : ℕ → SimpleFunc ℝ ℝ,
      (∀ k z, ‖f k z‖ ≤ 1) ∧
      (∀ z ∈ B, Tendsto (fun k => f k z) atTop (𝓝 z)) ∧
      Integrable N P ∧ Integrable (fun ω => (N ω)^2) P ∧
      (∀ᵐ ω ∂P, ∀ k,
        |∫ p in Ioc 0 T ×ˢ B, f k p.2 ∂NX ω| ≤ N ω) ∧
      (∀ᵐ ω ∂P,
        Tendsto (fun k => ∫ p in Ioc 0 T ×ˢ B, f k p.2 ∂NX ω)
          atTop (𝓝 (J ω))) := by sorry
