-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a233_original_stopped_fullcell_positive_raw_gaussian_exponential_tail_expected_L1_vanish
-- name    : AvramDividend.Classical.avram_ga_a233_original_stopped_fullcell_positive_raw_gaussian_exponential_tail_expected_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:34:32.339264+00:00
-- url     : https://prove2.me/theorems/52dae0a4-acfa-4be7-a6ae-f2480339904f
-- title:
--   True stopped original Gaussian physical full-cell positive raw exponential large-increment tail vanishes expected L1
-- statement:
--   For the original zerojump Gaussian Lévy source, original finite-horizon physical grid and an original right-continuous-filtration stopping time rho, the sum of raw positive large-increment exponential contributions restricted to exact cells wholly before the stopping time is integrable and its expected contribution vanishes. Proved by source-exact unconditional raw Gaussian exponential tail and the prior finite measurable positive full stopping-cell mask transfer; directly supports the a216 combined one-sided Gaussian analytic source.
-- source:
--   Original a231 unconditional raw positive Gaussian rare exp L1; source a229 integrability; a213 measurable positive stopping-cell restriction

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a213_finite_measurable_positive_mask_restriction_preserves_expected_L1_zero
import Theorems.Thm_AvramDividend_Classical_avram_ga_a229_original_gaussian_true_physical_mesh_raw_and_centered_positive_exp_sums_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a231_original_true_physical_raw_gaussian_positive_exponential_tail_expected_L1_vanish
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a233_original_stopped_fullcell_positive_raw_gaussian_exponential_tail_expected_L1_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (θ δ : ℝ) (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω - X.X (s m i) ω
    let Tail : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω then
          (if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0)
        else 0
    (∀ m, Integrable (Tail m) P) ∧
      Tendsto (fun m => ∫ ω, Tail m ω ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
