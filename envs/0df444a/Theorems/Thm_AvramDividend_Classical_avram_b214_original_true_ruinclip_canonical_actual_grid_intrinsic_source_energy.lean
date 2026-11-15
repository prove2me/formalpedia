-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b214_original_true_ruinclip_canonical_actual_grid_intrinsic_source_energy
-- name    : AvramDividend.Classical.avram_b214_original_true_ruinclip_canonical_actual_grid_intrinsic_source_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:59:24.063064+00:00
-- url     : https://prove2.me/theorems/d6161470-1f25-412b-ae32-4b15042b2f84
-- title:
--   Original true ruin-clipped mixed intrinsic Gaussian and negative jump mesh energy for explicitly defined genuine source-marked cells
-- statement:
--   Under the original finite negative-activity spectrally negative Levy source, an actual true ruin-clipped finite random physical grid with bounded measurable monotone endpoints, exact original intrinsic Gaussian residual and compensated negative mark source limits, the genuine stopped mixed Gaussian-jump energy is integrable with its mesh-independent physical source bound. The mark selector is now the canonical literal finite filter of source cells containing genuine nonzero negative Lévy jumps, rather than an arbitrary input J with a separately assumed exact-characterisation predicate. Proved B210 supplies the stopped source bound, having already eliminated source-count measurability/Poisson domination and jump-free Gaussian drift premises; its residual increment square-integrability remains explicit.
-- source:
--   B210 original source with genuine finite marked-cell filter, original ruinclock and intrinsic noise limits.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b210_original_canonical_ruinclipped_mixed_energy_from_intrinsic_gaussian_source
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b214_original_true_ruinclip_canonical_actual_grid_intrinsic_source_energy
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
    (V : ℕ → Ω → ℝ)
    (d : ℝ) (R Jsmall : ℝ≥0 → Ω → ℝ)
    (grid : Ω → ℕ → ℝ≥0)
    (hGridMono : ∀ ω, Monotone (grid ω))
    (hGridMeas : ∀ i, Measurable (fun ω => grid ω i))
    (hGridBound : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ (n : ℝ≥0))
    (hGridEndpoints : ∀ ω i, i ∈ S →
      s i ω = grid ω i ∧ t i ω = grid ω (i + 1))
    (hRsrc : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j u ω)
        atTop (𝓝 (R u ω)))
    (hJsrc : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X j u ω)
        atTop (𝓝 (Jsmall u ω)))
    (hV : ∀ ω i, i ∈ S →
      V i ω = R (t i ω) ω - R (s i ω) ω)
    (hd : d = -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))
    (hInterior : ∀ ω i, i ∈ S →
      s i ω ≤ t i ω ∧
      (t i ω : ℝ≥0∞) < (κ k ω : ℝ≥0∞))
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
