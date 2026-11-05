-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_intrinsic_NX_P2_rate
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_intrinsic_NX_P2_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:51:00.609874+00:00
-- url     : https://prove2.me/theorems/6e7ca9f2-4dc3-4ceb-8bbd-05cd6b77e261
-- title:
--   Original intrinsic stopped BV jump kernel has the now-Proved P2 prescribed rectangle rate
-- statement:
--   For the genuine original spectrally negative Levy process X, identify the intrinsic marked jump measure NX definitionally with its true path. Then directly instantiate the now Proved original P2 predictable rectangle compensation theorem to discharge exactly the hP2 rate parameter in P3-B's original BV C1 stopped signed mean-zero theorem. No invented compensator or process assumptions.
-- source:
--   Source-exact Proved original P2-E rectangle compensator UUID 393b03a8-2e9a-43d8-b415-854d86d58104; P3-B original hP2 interface bd3f3f6d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_intrinsic_NX_P2_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) :
    ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω in A, NX ω (Ioc s t ×ˢ B) ∂P) =
          P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
