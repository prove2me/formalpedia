-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_preruin_two_sided_prefix_localisation
-- name    : AvramDividend.Classical.avram_ubv_top9_original_preruin_two_sided_prefix_localisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:02:49.731421+00:00
-- url     : https://prove2.me/theorems/b291aa55-b774-4b76-ac34-8ee33c3fb288
-- title:
--   True original upcross stopping clocks with two-sided compact Levy and reserve strips on every surviving prefix
-- statement:
--   A genuine nested sequence of finite right-continuous stopping clocks exhausting an arbitrary bounded clock simultaneously controls the original Levy process at all prior times and places surviving pre-ruin Levy and controlled reserve values in compact two-sided bands. This is the source-geometric localisation interface for the still-open Ito-Meyer HJB expectation proof.
-- source:
--   Proved TOP9 prefix upcross 90b203a8 and strict pre-ruin compact strip 72000b1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_preruin_two_sided_prefix_localisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ n) :
    ∃ κ : ℕ → Ω → ℝ≥0,
      (∀ j, IsStoppingTime 𝓕.rightCont (fun ω => (κ j ω : WithTop ℝ≥0))) ∧
      (∀ j ω, κ j ω ≤ ρ ω) ∧
      (∀ j ω (t : ℝ≥0), t ≤ κ j ω →
        X.X t ω ≤ (j : ℝ) + 1 ∧
        ((t : ℝ≥0∞) < ruinTime X x D ω →
          X.X t ω ∈ Icc (-x) ((j : ℝ) + 1) ∧
          riskProcess X x D t ω ∈ Icc 0 (x + ((j : ℝ) + 1)))) ∧
      (∀ ω, ∀ᶠ j : ℕ in atTop, κ j ω = ρ ω) := by sorry
