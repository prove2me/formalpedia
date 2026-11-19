-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_large_only_dirac_intrinsic_smallmark_any_stopped_grid_zero_ae
-- name    : AvramDividend.Classical.avram_ja18_large_only_dirac_intrinsic_smallmark_any_stopped_grid_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:07:17.977283+00:00
-- url     : https://prove2.me/theorems/703dab88-55c6-422b-a9a0-452f12f076ea
-- title:
--   Large-only Dirac jumps: all intrinsic small-band predictable stopped meshes vanish
-- statement:
--   For a physical spectrally negative Levy driver whose Levy measure is delta at -2 and with all nonzero path jump marks at most -1, the actual intrinsic smallband limit Jsmall is a.e. zero. Hence every finite predictable stopped mesh using only differences of Jsmall is a.e. zero, regardless of the grid, weights, or stopping clock. This isolates the genuine large-negative-mark gap in source-faithful physical Ito ledger witnesses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_large_only_dirac_intrinsic_smallmark_any_stopped_grid_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = Measure.dirac (-2 : ℝ))
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
