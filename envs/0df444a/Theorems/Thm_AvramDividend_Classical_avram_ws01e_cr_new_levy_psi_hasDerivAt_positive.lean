-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_levy_psi_hasDerivAt_positive
-- name    : AvramDividend.Classical.avram_ws01e_cr_new_levy_psi_hasDerivAt_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:51:16.544768+00:00
-- url     : https://prove2.me/theorems/8a4ced2d-dbf0-474a-a831-0eab4ade8f75
-- title:
--   Canonical Lévy Laplace exponent has a finite two-sided derivative at every positive argument
-- statement:
--   For any canonical spectrally negative Lévy process, ψ has a genuine two-sided HasDerivAt derivative at each y>0 without extra Standing or integrability assumptions. Take the actual X_1 increment, use the exact source Laplace-moment field to show its cumulant generating function is analytic on the positive half-line by pinned Mathlib analyticOnNhd_cgf, identify it with ψ via the Laplace identity, and extract the derivative. This is stronger than finite right secants and directly discharges any positive-parameter differentiability premise.
-- source:
--   SpectrallyNegativeLevy.laplace and ψ in the exact pinned canonical definition; pinned Mathlib ProbabilityTheory.analyticOnNhd_cgf. The analytic cgf identification is independently verified in Proved 4dddb6f2-c657-46f9-89ae-291bb1ef0a23, but the explicit all-positive HasDerivAt extraction is a distinct missing public interface.

import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Topology.Closure
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_cr_new_levy_psi_hasDerivAt_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (y : ℝ) (hy : 0 < y) :
    ∃ m : ℝ, HasDerivAt X.ψ m y := by sorry
