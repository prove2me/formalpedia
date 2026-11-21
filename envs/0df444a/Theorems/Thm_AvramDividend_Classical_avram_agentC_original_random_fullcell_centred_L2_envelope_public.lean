-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentC_original_random_fullcell_centred_L2_envelope_public
-- name    : AvramDividend.Classical.avram_agentC_original_random_fullcell_centred_L2_envelope_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:24:41.047424+00:00
-- url     : https://prove2.me/theorems/4fbda516-3a3f-4653-8e7f-1b6d8dce7315
-- title:
--   Public source: Original zerojump random complete Gaussian cell centred polynomial has integrable uniform envelope
-- statement:
--   The same-process original Gaussian path has an integrable squared supremum S over [0,n]; every physically bounded random complete grid cell has squared centred increment at most 4S and absolute increment at most 1+4S. Thus B = 1+8S+n is integrable uniformly over all random cell indices. This is the substantive L1 domination obstruction in the original physical stopped Gaussian polynomial residual; independent of any H cell coefficient.
-- source:
--   Original spectrally negative Lévy Gaussian finite-horizon martingale; path continuity, random physical cell moment domination, dominated convergence in Avram Dividend Classical. Public theorem required as a dependency of the original public a37; initial private publication cannot be imported into it by policy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentC_original_random_fullcell_centred_L2_envelope_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (i : ℕ → Ω → ℕ)
    (hEnd : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ + Δ ≤ (n : ℝ≥0))
    (Z : ℕ → Ω → ℝ)
    (hZeq : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
      Z m ω = X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c)
:
    ∃ B : Ω → ℝ, Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ m,
        |Z m ω| + (Z m ω)^2 +
          ((n : ℝ) / ((m : ℝ) + 1)) ≤ B ω) := by sorry
