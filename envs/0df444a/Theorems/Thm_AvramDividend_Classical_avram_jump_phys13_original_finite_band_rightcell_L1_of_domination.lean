-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_finite_band_rightcell_L1_of_domination
-- name    : AvramDividend.Classical.avram_jump_phys13_original_finite_band_rightcell_L1_of_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T01:23:41.991545+00:00
-- url     : https://prove2.me/theorems/a5c5c5b5-12cf-41cd-b137-10a89b2f90c6
-- title:
--   Fixed-cutoff original stopped jump right-cell error converges in physical L1 under a single full-horizon integrable majorant
-- statement:
--   For the actual negative jumps of the original process X.X, any stopped finite-cutoff right-cell source error vanishing when that cell has no cutoff jump and dominated by one integrable full-horizon envelope converges to zero in physical L1. The finite-band post-stop cell becomes empty pathwise by Proved 17e97019, and dominated convergence preserves F0 masks encoded in the error. The envelope must be justified from full-horizon finite-rate counts when this theorem is instantiated. This does not assert an epsilon-uniform estimate or handle the infinite-activity annulus L2 passage.
-- source:
--   PJ-PHYS13 necessary fixed-band original-source L1 step for canonical 0b1a879a, using Proved 17e97019; exclusive owned avram_jump_phys13 namespace.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_finite_cutoff_rightcell_eventually_void

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump_phys13_original_finite_band_rightcell_L1_of_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0) (e : ℕ → Ω → ℝ≥0)
    (heBound : ∀ k ω, e k ω ≤ T)
    (heTendsto : ∀ ω, Tendsto (fun k => e k ω) atTop (𝓝 (τ ω)))
    (F : ℕ → Ω → ℝ)
    (hFvanish : ∀ k ω,
      {u : ℝ≥0 | τ ω < u ∧ u ≤ e k ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((cut : ℝ) + 1))} = ∅ → F k ω = 0)
    (hFmeas : ∀ k, AEStronglyMeasurable (fun ω => |F k ω|) P)
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hDom : ∀ k, ∀ᵐ ω ∂P, |F k ω| ≤ B ω) :
    Tendsto (fun k => ∫ ω, |F k ω| ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
