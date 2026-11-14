-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a214_true_physical_fullcell_raw_centered_square_cross_expected_L1
-- name    : AvramDividend.Classical.avram_ga_a214_true_physical_fullcell_raw_centered_square_cross_expected_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:51:20.992804+00:00
-- url     : https://prove2.me/theorems/40607325-1b9f-48e0-b65e-64435357899b
-- title:
--   Exact original stopped fully pre-stop Gaussian raw-centred quadratic cross energy vanishes in expected absolute L1 via pure-mask transfer
-- statement:
--   For the original zero-Levy-measure Gaussian source, the physical raw increments R and drift-centred increments Z have a vanishing expected absolute sum of their squared differences across the actual uniform-grid cells fully before the stopping clock, along with integrability at every mesh. The exact true full pre-stop mask is retained. This is the missing unweighted energy estimate for a150; prove by stopped Gaussian variance ga39, square identity/Young inequality and the generic L1 transfer ga81. This direct source-exact version uses the public standalone pure Mathlib mask restriction theorem a213 rather than the unpublished a171 version.
-- source:
--   Original process X.X, true full physical mask, Proved ga39/ga81/ga82/ga85 and drift-square mass vanish.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a214_true_physical_fullcell_raw_centered_square_cross_expected_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let Cross : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        if s < ρ ω ∧ s + Δ ≤ ρ ω then |R^2 - Z^2| else 0
    (∀ m : ℕ, Integrable (Cross m) P) ∧
    Tendsto (fun m : ℕ => ∫ ω, Cross m ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
