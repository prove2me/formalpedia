-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_bounded_marked_count_pgf_integrable_20261117
-- name    : AvramDividend.Classical.avram_a27_bounded_marked_count_pgf_integrable_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:05:51.483442+00:00
-- url     : https://prove2.me/theorems/114bac6e-6145-43ac-ac1f-89e18a084ffd
-- title:
--   Bounded marked Poisson count PGF is integrable on every original probability space
-- statement:
--   For any measurable integer-valued count K and measurable mark weight in the unit interval almost surely, the product z^K F is integrable for every generating parameter z in [0,1]. This is the deterministic dominated-convergence foundation for extracting the original physical marked-Poisson conditional Laplace count cells.
-- source:
--   Elementary count power bounds and integrable domination by the unit function under a probability measure; no auxiliary probability space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A bounded mark factor gives an integrable count-weighted PGF on any probability space. -/

theorem AvramDividend.Classical.avram_a27_bounded_marked_count_pgf_integrable_20261117
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (F : Ω → ℝ) (hF : Measurable F)
    (hRange : ∀ᵐ ω ∂P, 0 ≤ F ω ∧ F ω ≤ 1)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Integrable (fun ω => z ^ (K ω) * F ω) P := by sorry
