-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gtop23_original_debut_cofinal_with_stopped_sigma
-- name    : AvramDividend.Classical.avram_gtop23_original_debut_cofinal_with_stopped_sigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T02:49:29.146875+00:00
-- url     : https://prove2.me/theorems/8c9cf17d-0ed3-42a0-8d40-7deddcc87cd3
-- title:
--   Original sampled lower-exit supremum of a genuine stopped Gaussian clock is cofinal
-- statement:
--   Necessary substantive compact-prefix cofinality lemma for Open f9caff29. A genuine original-process sampled lower-exit supremum that is a stopping time and lies below the physical horizon must equal it almost surely, using strict pre-supremum solvency, original stopped right-neighbourhood positivity, and a compact-prefix threshold contradiction. Explicit genuine stopping-time hypothesis for the clipping clock σ is required by the imported pathwise strict-prefix theorem.
-- source:
--   Reuses Proved avram_gclose17_original_debut_strict_earlier_postpayment, avram_gclose16_original_stopping_right_neighbourhood_strict_postpayment_preruin, avram_gclose16_original_compact_strict_sampled_exit_eventually_after_prefix, all pinned and source-exact.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gtop23_original_debut_cofinal_with_stopped_sigma
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσruin : ∀ ω, (σ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (r : ℕ → ℝ≥0)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U)
    (δ : ℕ → ℝ)
    (hδpos : ∀ j, 0 < δ j)
    (hδlim : Tendsto δ atTop (𝓝 (0 : ℝ)))
    (S : Ω → ℝ≥0)
    (hSstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (S ω : WithTop ℝ≥0)))
    (hSle : ∀ ω, S ω ≤ σ ω)
    (hSdef : ∀ ω,
      (S ω : WithTop ℝ≥0) = ⨆ j : ℕ,
        min (σ ω : WithTop ℝ≥0)
          (⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < δ j
            then (r k : WithTop ℝ≥0) else ⊤)) :
    ∀ᵐ ω ∂P, S ω = σ ω := by sorry
