-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_all_large_negative_marks_intrinsic_smallband_stopped_mesh_zero
-- name    : AvramDividend.Classical.avram_ja18_all_large_negative_marks_intrinsic_smallband_stopped_mesh_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:52:21.402101+00:00
-- url     : https://prove2.me/theorems/0ca67aad-fba3-4d64-9489-11539200998b
-- title:
--   General large-negative-mark intrinsic small-band stopped-mesh cancellation
-- statement:
--   For any original spectrally negative Levy driver having zero measure on (-1,0] and only jumps of size at most -1, the original intrinsic small-band compensated source converges almost surely to a process that is simultaneously zero at all times. Every finite stopped grid sum with arbitrary random weights built solely from differences of that intrinsic small-band limit is then almost surely zero. Includes all large-only negative-mark laws, not merely Dirac(-2). This is a source-faithful small-band omission result, not a full mixed Ito cash inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_all_large_negative_marks_intrinsic_smallband_stopped_mesh_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hνsmall : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hLarge : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
       X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (WJ : ℕ → Ω → ℝ) (σ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, (∑ i ∈ S,
      (if σ ω ≤ a i then 0 else WJ i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω)) = 0 := by sorry
