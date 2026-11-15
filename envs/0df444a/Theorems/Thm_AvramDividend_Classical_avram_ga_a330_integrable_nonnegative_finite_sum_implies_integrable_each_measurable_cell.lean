-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a330_integrable_nonnegative_finite_sum_implies_integrable_each_measurable_cell
-- name    : AvramDividend.Classical.avram_ga_a330_integrable_nonnegative_finite_sum_implies_integrable_each_measurable_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:06:05.288197+00:00
-- url     : https://prove2.me/theorems/2fc402db-26ad-4b8d-804e-2bd6654fc857
-- title:
--   Each nonnegative measurable finite Gaussian cell is integrable if its finite sum is integrable
-- statement:
--   For a finite family of measurable nonnegative real source functions, integrability of the sum implies integrability of every summand by the nonnegative single-summand bound and Integrable.mono. The source lemma is used with actual original Gaussian stopped full-cell raw squared increments in a311, whose monolithic integrability proof was stopped by a CLI complexity gate.
-- source:
--   General finite nonnegative Bochner integrability domination, original Gaussian true raw finite sum integrability a243.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a330_integrable_nonnegative_finite_sum_implies_integrable_each_measurable_cell
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Finset ℕ) (f : ℕ → Ω → ℝ)
    (hfMeas : ∀ i ∈ S, Measurable (f i))
    (hfPos : ∀ i ∈ S, ∀ ω, 0 ≤ f i ω)
    (hSum : Integrable (fun ω => ∑ i ∈ S, f i ω) P) :
    ∀ i ∈ S, Integrable (f i) P := by sorry
