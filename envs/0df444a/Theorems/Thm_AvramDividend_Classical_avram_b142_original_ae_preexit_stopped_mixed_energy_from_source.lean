-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b142_original_ae_preexit_stopped_mixed_energy_from_source
-- name    : AvramDividend.Classical.avram_b142_original_ae_preexit_stopped_mixed_energy_from_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:11:43.5473+00:00
-- url     : https://prove2.me/theorems/bfa78f2e-df63-4fda-a7b0-b8a9e944bf50
-- title:
--   Original pre-ruin and pre-upcross stopped source mesh mixed Gaussian/negative-mark energy under conull Poisson count dominance
-- statement:
--   For the true original spectrally negative Lévy reserve source, finite physically stopped strictly interior cells before the genuine source upcrossing, Gaussian residual increments and negative mark contacts satisfy the same compact mixed source square-energy L1 and expectation estimate as Proved B68. This upgraded theorem replaces B68’s all-path real-toReal marked Poisson count domination by an almost-everywhere original source count domination, through the prepared B141 conull mixed energy theorem. All original pre-exit lower/upper source bounds and controlled-cell separation remain unchanged. This correctly handles exceptional original sample paths and is the crucial link between physical Poisson mark selection and the true ruin-clipped B73 source energy required for stopped Ito verification. Publication waits for B141 Proved.
-- source:
--   Prepared B141 conull original mixed source energy and Proved B67 physical pre-exit source compact bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
import Theorems.Thm_AvramDividend_Classical_avram_b58_original_selected_negative_jump_cells_uniform_count_L1
import Theorems.Thm_AvramDividend_Classical_avram_b141_original_ae_compact_mixed_source_uniform_expected_square_energy
import Theorems.Thm_AvramDividend_Classical_avram_b67_original_preupper_X_centered_cell_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original pre-ruin strict interior stopped source has uniform mixed energy under conull marked-grid count domination. -/

theorem AvramDividend.Classical.avram_b142_original_ae_preexit_stopped_mixed_energy_from_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (x b d : ℝ) (hxb : 0 ≤ x + b)
    (hCell : ∀ ω i, i ∈ S → s i ω ≤ t i ω ∧ t i ω ≤ T)
    (hLower : ∀ ω i, i ∈ S →
      -x ≤ X.X (s i ω) ω ∧ -x ≤ X.X (t i ω) ω)
    (hBeforeUp : ∀ ω i, i ∈ S →
      (s i ω : ℝ≥0∞) < twoSidedExitUpTime X b ω ∧
      (t i ω : ℝ≥0∞) < twoSidedExitUpTime X b ω)
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
        (x + b + (T : ℝ) * |X.c|)^2 * ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by sorry
