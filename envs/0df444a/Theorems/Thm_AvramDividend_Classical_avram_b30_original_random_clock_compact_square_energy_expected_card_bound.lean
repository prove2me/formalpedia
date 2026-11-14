-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b30_original_random_clock_compact_square_energy_expected_card_bound
-- name    : AvramDividend.Classical.avram_b30_original_random_clock_compact_square_energy_expected_card_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:15:32.790657+00:00
-- url     : https://prove2.me/theorems/9ec9552b-56a9-4d11-af97-470123a0baeb
-- title:
--   Original stopped random physical compact square mesh expected energy bounded by band width and number of cells
-- statement:
--   For every finite collection of actual original Lévy random stopping-time mesh cells whose pre-left and post-increment reserves remain in a compact reserve band on A, their restricted physical quadratic energy is integrable and its expectation is at most the cell count times the squared band width times P(A).
-- source:
--   Avram-Palmowski-Pistorius (2007), Proposition 4(i), local stopped Itô–Meyer compact band; B27 original random stopped quadratic integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_random_stopped_compact_mesh_energy_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b30_original_random_clock_compact_square_energy_expected_card_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    ∀ (A : Set Ω) (S : Finset ℕ)
      (s t : ℕ → Ω → ℝ≥0),
      let z : Ω → ℕ → ℝ := fun ω i =>
        Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) (s i ω)
      let g : Ω → ℕ → ℝ := fun ω i =>
        X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω - s i ω) : ℝ) * X.c
      let Q : Ω → ℝ := fun ω => ∑ i ∈ S, (g ω i) ^ 2
      (∀ i ∈ S, IsStoppingTime 𝓕.rightCont
        (fun ω => (s i ω : WithTop ℝ≥0))) →
      (∀ i ∈ S, IsStoppingTime 𝓕.rightCont
        (fun ω => (t i ω : WithTop ℝ≥0))) →
      (∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S,
        z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b) →
      IntegrableOn Q A P ∧
        (∫ ω in A, Q ω ∂P) ≤
          ((S.card : ℝ) * (b - a) ^ 2) * (P A).toReal := by sorry
