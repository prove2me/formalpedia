-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b141_original_ae_compact_mixed_source_uniform_expected_square_energy
-- name    : AvramDividend.Classical.avram_b141_original_ae_compact_mixed_source_uniform_expected_square_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:07:56.551792+00:00
-- url     : https://prove2.me/theorems/bbbef8b9-b9aa-4605-a6ff-47e5b0591429
-- title:
--   Original mixed Gaussian and genuine marked-grid finite-mesh squared-source energy under conull Poisson count domination
-- statement:
--   For the original finite-negative-activity spectrally negative Levy source, finite physical stopped-grid source intervals and their intrinsic Gaussian and marked contact channels, assume exact pathwise compact source bounds and physical original marked-cell membership as in the Proved B61 theorem. Replace only B61’s unnecessarily strong domination of the marked-cell count by the real Poisson source count on every path with an almost-everywhere domination. B140 provides finite first moment and expected bound for this measurable marked-grid cardinal under conull original Poisson domination. The original Proved B60 pathwise square split and integrable Gaussian and elapsed-clock components then give the same uniform-in-mesh expected squared source-energy estimate and L1 integrability, without imposing full-source finite marks on exceptional paths. This is the proper input to the original pre-ruin B68/B73 stopped Ito energy route. Publication waits for B140 Proved.
-- source:
--   Prepared B140 a.e. physical marked Poisson count expectation plus Proved B60 physical Gaussian and marked-cell source square split.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
import Theorems.Thm_AvramDividend_Classical_avram_b140_original_ae_selected_negative_jump_cells_uniform_count_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original mixed finite Gaussian and marked-grid mesh square-energy bound with only conull source count domination. -/

theorem AvramDividend.Classical.avram_b141_original_ae_compact_mixed_source_uniform_expected_square_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (d a b : ℝ) (hab : a ≤ b)
    (hJsub : ∀ ω, J ω ⊆ S)
    (hJmeas : Measurable (fun ω : Ω => ((J ω).card : ℝ)))
    (hJdom : ∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
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
