-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b75_original_true_ruinclipped_stopping_grid_mixed_energy
-- name    : AvramDividend.Classical.avram_b75_original_true_ruinclipped_stopping_grid_mixed_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:56:25.760336+00:00
-- url     : https://prove2.me/theorems/0aed1ac7-1e88-42f5-a935-2adc25c3c3ee
-- title:
--   Original actual ruin-clipped pre-ruin stopping-grid mixed source expected square energy
-- statement:
--   On the original finite-activity mixed Lévy source with its own probability and right-continuous filtration, any finite set of genuine stopping-time cells lying strictly inside the physical ruin-clipped and source-upcrossing clock has mesh-cardinality-independent expected square energy for drift-corrected physical source increments. Actual stop times provide both source and duration measurability via B74; B72 gives lower source bounds from admissible pre-ruin reserve and original upper source-exit clipping; B70 gives duration integrability; B68 gives energy using selected actual negative-jump-cell count and Gaussian-no-contact energy. Assumes explicitly a physically valid no-jump Gaussian source decomposition, original selected marked count domination, and Gaussian energy integrability. The final potentially unbounded negative ruin-crossing jump is excluded; no Gaussian independence or global second mark moment is asserted.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 4(i) Section 5.4; original B72 B68 B70 B74 physical stopped-clock source energy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b61_original_compact_mixed_source_uniform_expected_square_energy
import Theorems.Thm_AvramDividend_Classical_avram_b72_original_true_ruinclock_strict_interior_source_envelope
import Theorems.Thm_AvramDividend_Classical_avram_b70_original_bounded_physical_duration_square_energy_integrable
import Theorems.Thm_AvramDividend_Classical_avram_b74_original_true_stopping_grid_mixed_source_duration_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b75_original_true_ruinclipped_stopping_grid_mixed_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (hx : 0 < x) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (k : ℕ) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (d : ℝ)
    (hInterior : ∀ ω i, i ∈ S →
      s i ω ≤ t i ω ∧
      (t i ω : ℝ≥0∞) < (κ k ω : ℝ≥0∞))
    (hJsub : ∀ ω, J ω ⊆ S)
    (hJmeas : Measurable (fun ω : Ω => ((J ω).card : ℝ)))
    (hJdom : ∀ ω : Ω, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal)
    (hNoJump : ∀ ω i, i ∈ S → i ∉ J ω →
      X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
          V i ω + d * ((t i ω - s i ω : ℝ≥0) : ℝ))
    (hsStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (s i ω : WithTop ℝ≥0)))
    (htStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (t i ω : WithTop ℝ≥0)))
    (hGI : Integrable (fun ω => ∑ i ∈ S, (V i ω)^2) P) :
    let E : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
    let G : Ω → ℝ := fun ω => ∑ i ∈ S, (V i ω)^2
    let D : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
    Integrable E P ∧ (∫ ω, E ω ∂P) ≤
      2 * (∫ ω, G ω ∂P) + 2 * d^2 * (∫ ω, D ω ∂P) +
        (x + ((k : ℝ) + 1) + ((n : ℝ≥0) : ℝ) * |X.c|)^2 * (((n : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by sorry
