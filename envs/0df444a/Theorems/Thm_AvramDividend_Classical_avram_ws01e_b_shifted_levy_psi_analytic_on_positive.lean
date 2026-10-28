-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_shifted_levy_psi_analytic_on_positive
-- name    : AvramDividend.Classical.avram_ws01e_b_shifted_levy_psi_analytic_on_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:05:21.372168+00:00
-- url     : https://prove2.me/theorems/4dddb6f2-c657-46f9-89ae-291bb1ef0a23
-- title:
--   Actual spectrally negative Lévy Laplace exponent is analytic after a positive Esscher shift
-- statement:
--   For a genuine spectrally negative Lévy process with its actual Lévy exponential-moment law, the shifted exponent beta ↦ psi(phi+beta)-q is real analytic at every positive beta whenever phi>0. Prove directly by the cumulant-generating function of X at time one, the exact Laplace exponent identity, and composition; no regularity or independence assumption about the exponent is supplied.
-- source:
--   Mathlib ProbabilityTheory.analyticOnNhd_cgf and AnalyticOnNhd.fun_comp; SpectrallyNegativeLevy.laplace from canonical Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy; Kuznetsov–Kyprianou–Rivero (2013), Section 2.1, Laplace exponent / Esscher transform.

import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Topology.Closure
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_shifted_levy_psi_analytic_on_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q : ℝ) (hφ : 0 < φ) :
    AnalyticOnNhd ℝ (fun β : ℝ => X.ψ (φ + β) - q) (Set.Ioi 0) := by sorry
