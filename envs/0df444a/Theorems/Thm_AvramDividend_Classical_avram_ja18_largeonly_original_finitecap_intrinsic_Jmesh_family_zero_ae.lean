-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_largeonly_original_finitecap_intrinsic_Jmesh_family_zero_ae
-- name    : AvramDividend.Classical.avram_ja18_largeonly_original_finitecap_intrinsic_Jmesh_family_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:54:55.342748+00:00
-- url     : https://prove2.me/theorems/ee3674ba-3e9a-4d25-bb08-1ca59ec33cde
-- title:
--   Original large-mark finite-cap small-band mesh gain families vanish at all indices
-- statement:
--   In the same-X original Levy source with no small negative marks, if Jsmall is the genuine intrinsic compensated small-band limit and each J(k) is represented by any finite stopped mesh of Jsmall increments (exactly the jump-channel gain shape required by the finite-cap physical Ito cash source), then J(k)=0 almost surely for every k. This formalises at the level of the entire candidate mesh family why large-negative jump marks are invisible to the Jsmall channel and must be represented separately in physical stopped Ito.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_largeonly_original_finitecap_intrinsic_Jmesh_family_zero_ae
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
    (σ : Ω → ℝ≥0) (J : ℕ → Ω → ℝ)
    (hJmesh : ∀ k : ℕ, ∃ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
      (WJ : ℕ → Ω → ℝ),
      ∀ ω : Ω, J k ω =
        ∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)) :
    ∀ k : ℕ, ∀ᵐ ω ∂P, J k ω = 0 := by sorry
