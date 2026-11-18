-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_count_HasLaw_pgf_exact_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_count_HasLaw_pgf_exact_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T21:57:43.327133+00:00
-- url     : https://prove2.me/theorems/009ff568-2492-4391-adcc-d5598ecae857
-- title:
--   Exact original physical Poisson count generating function transported through its actual HasLaw
-- statement:
--   For a measurable source-space random count K whose actual law on its unchanged probability measure P is Poisson with rate r, the integral of z to the K equals exp(r(z-1)) for every real z. This is the count-only generating-function boundary of the original physical marked-jump PGF. It transfers integrals through HasLaw without introducing any different probability space.
-- source:
--   Pinned Mathlib ProbabilityTheory.HasLaw.integral_comp, Poisson.Basic, and the existing Proved general Poisson PGF AvramDividend.Classical.chat06_poisson_count_pgf_general.

import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_physical_count_HasLaw_pgf_exact_20261117
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ) (r : ℝ≥0)
    (hLaw : HasLaw K (poissonMeasure r) P)
    (z : ℝ) :
    (∫ ω, z ^ (K ω) ∂P) = Real.exp ((r : ℝ) * (z - 1)) := by sorry
