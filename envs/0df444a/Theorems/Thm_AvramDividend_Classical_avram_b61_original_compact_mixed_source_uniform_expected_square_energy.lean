-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b61_original_compact_mixed_source_uniform_expected_square_energy
-- name    : AvramDividend.Classical.avram_b61_original_compact_mixed_source_uniform_expected_square_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:36:00.473849+00:00
-- url     : https://prove2.me/theorems/586655d1-98a8-49bb-b06b-fc1746ae1dbf
-- title:
--   True original finite-activity compact Gaussian-jump stopped physical source squared energy uniformly bounded over arbitrary fine grids
-- statement:
--   On the actual finite-activity spectrally negative Lévy path, suppose the original drift-corrected increments split on cells with no physical negative jump into the same-path Gaussian residual plus deterministic drift correction, and on true negative-jump-bearing cells are spatially bounded by a compact band. Assume those selected jump cells inject into actual original negative marked jumps and the genuine Gaussian and duration quadratic energies are integrable. The full original drift-corrected finite-mesh square energy is then integrable and bounded in expectation by twice the Gaussian energy plus twice the squared drift-duration energy plus the band-width squared times the true Lévy jump intensity and physical horizon, independently of mesh cardinality.
-- source:
--   Proved B60 actual finite-source pathwise Gaussian-jump quadratic split, B58 original true marked negative jump count exact expectation budget, pinned Mathlib finite sums and integral monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
import Theorems.Thm_AvramDividend_Classical_avram_b58_original_selected_negative_jump_cells_uniform_count_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b61_original_compact_mixed_source_uniform_expected_square_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (d a b : ℝ) (hab : a ≤ b)
    (hJsub : ∀ ω, J ω ⊆ S)
    (hJmeas : Measurable (fun ω : Ω => ((J ω).card : ℝ)))
    (hJdom : ∀ ω : Ω, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal)
    (hNoJump : ∀ ω i, i ∈ S → i ∉ J ω →
      X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
          V i ω + d * ((t i ω - s i ω : ℝ≥0) : ℝ))
    (hJump : ∀ ω i, i ∈ S → i ∈ J ω →
      |X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c| ≤ b - a)
    (hEmeas : Measurable (fun ω =>
      ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2))
    (hGI : Integrable (fun ω => ∑ i ∈ S, (V i ω)^2) P)
    (hDI : Integrable (fun ω => ∑ i ∈ S,
      (((t i ω - s i ω : ℝ≥0) : ℝ))^2) P) :
    let E : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
    let G : Ω → ℝ := fun ω => ∑ i ∈ S, (V i ω)^2
    let D : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
    Integrable E P ∧ (∫ ω, E ω ∂P) ≤
      2 * (∫ ω, G ω ∂P) + 2 * d^2 * (∫ ω, D ω ∂P) +
        (b-a)^2 * ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by sorry
