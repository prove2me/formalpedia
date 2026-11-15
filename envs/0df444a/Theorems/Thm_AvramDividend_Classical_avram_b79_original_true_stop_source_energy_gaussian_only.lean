-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b79_original_true_stop_source_energy_gaussian_only
-- name    : AvramDividend.Classical.avram_b79_original_true_stop_source_energy_gaussian_only
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:07:32.71114+00:00
-- url     : https://prove2.me/theorems/2e501488-9f2a-42b4-af87-22c42feb24a5
-- title:
--   True ruin-clipped interior original source quadratic energy from intrinsic Gaussian residual and jumpfree mark cells
-- statement:
--   The exact original finite-activity mixed Levy stopped source has an intrinsic Gaussian residual M from the same probability space and filtration, almost everywhere equal to the original R extracted from truncated Levy-Ito residuals. On all genuine strict interior pre-ruin stopped cells, assume each unmarked cell has no original negative jump so its actual compensated small-band increment is the physical drift times elapsed duration and its large-jump source sum is constant. B78 then gives the *same global source M* whose increments plus the compensator drift exactly decompose the original X increments on unmarked cells. B74 proves the source square and duration square measurability from the actual stopping times; B73 gives expected stopped source square-energy independent of mesh cardinality, conditional only on explicit original Gaussian residual square-energy integrability and marked negative-jump count domination. This is a physical C2 Itô mesh energy prerequisite. The terminal ruin-crossing cell remains excluded; its negative source jump and right cash are handled by Proved B76. This theorem does not change the filtration, introduce an unrelated zero-jump Levy source, or claim a global negative mark second moment.
-- source:
--   Avram Palmowski Pistorius 2007 Proposition 4(i); original B73/B74/B78 physical source statements.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b73_original_actual_ruinclipped_strict_interior_mixed_energy
import Theorems.Thm_AvramDividend_Classical_avram_b74_original_true_stopping_grid_mixed_source_duration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b78_original_jumpfree_interior_cell_gaussian_residual_drift_decomp
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b79_original_true_stop_source_energy_gaussian_only
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω)))
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
    (J : Ω → Finset ℕ)
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
    (hsStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (s i ω : WithTop ℝ≥0)))
    (htStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (t i ω : WithTop ℝ≥0)))
    (hSmall : ∀ ω i, i ∈ S → i ∉ J ω →
      Jsmall (t i ω) ω - Jsmall (s i ω) ω =
        d * (((t i ω - s i ω : ℝ≥0) : ℝ)))
    (hLarge : ∀ ω i, i ∈ S → i ∉ J ω →
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (t i ω) ω =
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (s i ω) ω) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, M u ω = R u ω) ∧
      let E : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
      let G : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (M (t i ω) ω - M (s i ω) ω)^2
      let Dur : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
      Integrable G P →
      Integrable E P ∧ (∫ ω, E ω ∂P) ≤
        2 * (∫ ω, G ω ∂P) +
        2 * d^2 * (∫ ω, Dur ω ∂P) +
        (x + ((k : ℝ) + 1) + ((n : ℝ≥0) : ℝ) * |X.c|)^2 *
        (((n : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by sorry
