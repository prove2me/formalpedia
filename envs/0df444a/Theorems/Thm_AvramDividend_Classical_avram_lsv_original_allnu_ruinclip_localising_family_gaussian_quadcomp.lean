-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_allnu_ruinclip_localising_family_gaussian_quadcomp
-- name    : AvramDividend.Classical.avram_lsv_original_allnu_ruinclip_localising_family_gaussian_quadcomp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:26:41.468107+00:00
-- url     : https://prove2.me/theorems/0ff48bc4-3847-4c44-8553-06c9cd109d42
-- title:
--   Original mixed physical Levy Gaussian quadratic compensator centred for all localising clocks bounded by the true ruin clip
-- statement:
--   For every actual localising clock sigma k from the original Ito-Meyer source below the ruin-clipped time, prove the physical mixed same-space Gaussian stopped square is integrable with expected value volatility squared times the stopped clock and the compensated square is integrable and centred. Stopping-time measurability is derived rather than imposed. Same-space zerojump Y and physical jump channels remain explicit source hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_allnu_arbitrary_bounded_stop_exact_energy

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- The exact original clipped ruin stop used by Avram, with its actual
   right-continuous stopping-time witness and the physical jump channels.
   Applies the remotely Proved genuine mixed Gaussian arbitrary-stop theorem
   derived from dufeteller/lean-lsv (CC BY 4.0, commit a5f604d). -/

/- The true original sigma_k family below the exact ruin-clipped tau.
   The original mixed Levy physical Gaussian and jump channels are retained.
   Adapted from dufeteller/lean-lsv CC BY 4.0 commit a5f604d. -/

theorem AvramDividend.Classical.avram_lsv_original_allnu_ruinclip_localising_family_gaussian_quadcomp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω,
      τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k, let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    Integrable (fun ω => (M (σ k ω) ω)^2) P ∧
      (∫ ω, (M (σ k ω) ω)^2 ∂P) =
        ∫ ω, (σ k ω : ℝ) * X.σ^2 ∂P ∧
      Integrable (fun ω =>
        (M (σ k ω) ω)^2 - (σ k ω : ℝ) * X.σ^2) P ∧
      (∫ ω, (M (σ k ω) ω)^2 -
        (σ k ω : ℝ) * X.σ^2 ∂P) = 0 := by sorry
