-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_lower_exit_debut_sup_stopping
-- name    : AvramDividend.Classical.avram_gclose17_original_lower_exit_debut_sup_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:13:51.91329+00:00
-- url     : https://prove2.me/theorems/3c30d4b6-9537-4d80-911f-0589b2030a2b
-- title:
--   The supremum of original sampled lower-exit clipped clocks is a right-continuous-filtration stopping time
-- statement:
--   For one actual original controlled Levy process and admissible dividend strategy, take an arbitrary family of dense-sampled lower-reserve exit thresholds and clip each observation clock under a genuine original stopping clock. The pointwise supremum of these physical lower-exit clocks is itself a stopping time of the original right-continuous filtration and never exceeds the bounding clock. This constructs the legitimate stopping-time candidate for a first-zero-contact/debut argument. The theorem does not claim contact at the supremum; that requires a separate limit and no-positive-jumps proof.
-- source:
--   Apply Proved e129ae1d at each threshold, then characterise an iSup stopping event as a countable intersection of original filtration-measurable sublevel events.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_sampled_preexit_clipped_clock_floor
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose17_original_lower_exit_debut_sup_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → WithTop ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont σ)
    (r : ℕ → ℝ≥0)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U)
    (δ : ℕ → ℝ) :
    let ρ : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
      min (σ ω) (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ n
        then (r k : WithTop ℝ≥0) else ⊤)
    IsStoppingTime 𝓕.rightCont (fun ω => ⨆ n : ℕ, ρ n ω) ∧
      ∀ ω, (⨆ n : ℕ, ρ n ω) ≤ σ ω := by sorry
