-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentC_original_random_fullcell_centred_AE_limit_public
-- name    : AvramDividend.Classical.avram_agentC_original_random_fullcell_centred_AE_limit_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:24:41.403159+00:00
-- url     : https://prove2.me/theorems/cee9917e-44bc-4684-b041-9f8505e726da
-- title:
--   Public source: Original zerojump centred random physical full-cell increment tends to zero pathwise
-- statement:
--   The original X, arbitrary random i_m with actual complete-cell endpoint at most n, original uniform Delta and same-process centred Z. The original zerojump Gaussian increment is a.e continuous uniformly at random short clock gap; removing deterministic drift of size Delta yields a.e convergence to zero. This is a genuine time-index stochastic continuity obligation useful for the canonical physical Gaussian stochastic-grid source.
-- source:
--   Original spectrally negative Lévy Gaussian finite-horizon martingale; path continuity, random physical cell moment domination, dominated convergence in Avram Dividend Classical. Public theorem required as a dependency of the original public a37; initial private publication cannot be imported into it by policy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentC_original_random_fullcell_centred_AE_limit_public
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
    ∀ᵐ ω ∂P, Tendsto (fun m => Z m ω) atTop (nhds (0 : ℝ)) := by sorry
