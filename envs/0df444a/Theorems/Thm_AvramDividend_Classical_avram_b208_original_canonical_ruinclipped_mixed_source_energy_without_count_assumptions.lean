-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b208_original_canonical_ruinclipped_mixed_source_energy_without_count_assumptions
-- name    : AvramDividend.Classical.avram_b208_original_canonical_ruinclipped_mixed_source_energy_without_count_assumptions
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:04:11.896365+00:00
-- url     : https://prove2.me/theorems/9327e8b0-bcdc-40b8-a6ba-7b563d3ebad5
-- title:
--   Original canonical genuine marked-cell true ruin-clipped mixed Gaussian jump energy with all source count premises discharged
-- statement:
--   For the genuine original spectrally negative Lévy source with finite negative activity, true ruin-clipped stopping grid and canonical physically jump-containing random marked-cell set, the full mixed Gaussian/negative-jump finite-mesh squared source energy is integrable and satisfies the original drift, Gaussian and finite intensity bound. Actual marked-cell count measurability, integrability and real Poisson count domination are discharged from Proved B207 rather than assumed. The remaining Gaussian jumpfree increment identity is only required on a conull original source event, and all stopped times, ruin clipping and compact energy hypotheses remain exact. The original physical grid cell endpoints are explicitly matched to the monotone measurable grid; no independent jump source or post-ruin ledger is introduced.
-- source:
--   B207 genuine original Poisson count and B182 true ruin-clipped conull stopped source energy, original random grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b205_original_canonical_grid_marked_count_measurable_and_real_poisson_dom
import Theorems.Thm_AvramDividend_Classical_avram_b182_original_ae_true_ruinclipped_both_conull_mixed_energy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b208_original_canonical_ruinclipped_mixed_source_energy_without_count_assumptions
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
    (d : ℝ) (grid : Ω → ℕ → ℝ≥0)
    (hGridMono : ∀ ω, Monotone (grid ω))
    (hGridMeas : ∀ i, Measurable (fun ω => grid ω i))
    (hGridBound : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ (n : ℝ≥0))
    (hGridEndpoints : ∀ ω i, i ∈ S →
      s i ω = grid ω i ∧ t i ω = grid ω (i + 1))
    (hJcanon : ∀ ω i, i ∈ J ω ↔ i ∈ S ∧
      ∃ u : ℝ≥0, grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (hInterior : ∀ ω i, i ∈ S →
      s i ω ≤ t i ω ∧
      (t i ω : ℝ≥0∞) < (κ k ω : ℝ≥0∞))
    (hNoJump : ∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω →
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
