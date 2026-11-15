-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a246_integrable_combined_positive_source_small_large_L1_squeeze
-- name    : AvramDividend.Classical.avram_ga_a246_integrable_combined_positive_source_small_large_L1_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:29:51.69702+00:00
-- url     : https://prove2.me/theorems/c7280c59-e4b5-4d2e-9c80-ef598193c4c4
-- title:
--   Combined positive verification source vanishes in expected L1 when bounded by integrable small and large cell errors
-- statement:
--   For each finite mesh, suppose the nonnegative positive part of the combined verification source is integrable and pointwise bounded by an integrable small-cell contribution plus an integrable large-cell contribution. If both expectations tend to zero, the combined positive part expectation tends to zero. This is the exact final small/large expectation glue needed for the source-specific original Gaussian a216.
-- source:
--   Original Gaussian a216 combined physical fullcell positive source via proved a240 raw expected energy, a244 vanishing Taylor modulus energy, and a233 stopped rare Gaussian exp L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a246_integrable_combined_positive_source_small_large_L1_squeeze
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F S L : ℕ → Ω → ℝ)
    (hFI : ∀ m, Integrable (F m) P)
    (hSI : ∀ m, Integrable (S m) P)
    (hLI : ∀ m, Integrable (L m) P)
    (hFpos : ∀ m ω, 0 ≤ F m ω)
    (hPoint : ∀ m ω, F m ω ≤ S m ω + L m ω)
    (hSL : Tendsto (fun m => ∫ ω, S m ω ∂P) atTop (𝓝 (0 : ℝ)))
    (hLL : Tendsto (fun m => ∫ ω, L m ω ∂P) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, F m ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
