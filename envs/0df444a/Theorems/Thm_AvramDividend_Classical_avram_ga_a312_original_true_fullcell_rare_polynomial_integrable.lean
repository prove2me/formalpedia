-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a312_original_true_fullcell_rare_polynomial_integrable
-- name    : AvramDividend.Classical.avram_ga_a312_original_true_fullcell_rare_polynomial_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:28:25.052456+00:00
-- url     : https://prove2.me/theorems/3166dff7-a315-4332-907f-de29da46b1b2
-- title:
--   Actual original Gaussian fully stopped physical rare polynomial source integrable for every mesh
-- statement:
--   On every original finite-horizon physical Gaussian mesh, the rare-event polynomial sum consisting of the compact source 1, absolute raw increment and centred quadratic is integrable over the original law, restricted to wholly pre-stop cells and a fixed raw increment threshold. Original adaptedness, stopping-time measurability, true physical fullcell raw-square integrability a243 and general finite-mesh polynomial domination a311 prove this without assumptions about small drift or asymptotics. Discharges the explicit integrability premise in the expected rare-polynomial a304.
-- source:
--   True source a243 stopped full raw energy and a311 general masked Gaussian polynomial integrability, actual X adapted and rho stopping time.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a243_original_stopped_fullcell_raw_quadratic_energy_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a311_masked_Gaussian_polynomial_finite_mesh_integrable_from_raw_square
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a312_original_true_fullcell_rare_polynomial_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω-X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      R m i ω - (Δ m : ℝ) * X.c
    let Poly : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω) ∧
           δ ≤ |R m i ω| then
          1 + |R m i ω| + (Z m i ω)^2 / 2 else 0
    ∀ m, Integrable (Poly m) P := by sorry
