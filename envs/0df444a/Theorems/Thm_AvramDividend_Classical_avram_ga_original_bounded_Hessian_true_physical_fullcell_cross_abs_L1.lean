-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_bounded_Hessian_true_physical_fullcell_cross_abs_L1
-- name    : AvramDividend.Classical.avram_ga_original_bounded_Hessian_true_physical_fullcell_cross_abs_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:49:15.641486+00:00
-- url     : https://prove2.me/theorems/ba8830b1-8dab-4e25-b42b-cc4dcceb6769
-- title:
--   Bounded Hessian masked true physical Gaussian square cross vanishes in expected absolute value
-- statement:
--   For a spectrally negative jump-free Lévy process, any uniformly bounded predictable-like Hessian multiplier on full stopped physical grid cells produces an expected-absolute-valued sum of raw-minus-centred Gaussian increment squares tending to zero, provided the weighted sums are integrable. Import and combine proved physical-cross mean bound a214 and bounded Hessian finite-sum absolute inequality a88; preserve exact stopping mask and physical-grid definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_bounded_Hessian_true_physical_fullcell_cross_abs_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
       (fun ω => (ρ ω : WithTop ℝ≥0)))
    (H : ℕ → ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ m ω i, i < m → |H m i ω| ≤ K) :
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (Finset.range m).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        if s < ρ ω ∧ s + Δ ≤ ρ ω
        then H m i ω / 2 * (R ^ 2 - Z ^ 2) else 0)
    (∀ m, Integrable (fun ω => |B m ω|) P) →
    Tendsto (fun m => ∫ ω, |B m ω| ∂P) atTop (nhds (0 : ℝ)) := by sorry
