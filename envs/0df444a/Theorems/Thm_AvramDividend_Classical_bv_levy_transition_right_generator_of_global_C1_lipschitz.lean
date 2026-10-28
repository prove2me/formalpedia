-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_levy_transition_right_generator_of_global_C1_lipschitz
-- name    : AvramDividend.Classical.bv_levy_transition_right_generator_of_global_C1_lipschitz
-- status  : Open
-- author  : @WillR
-- created : 2026-10-25T22:34:53.121769+00:00
-- url     : https://prove2.me/theorems/b56e7174-ebfe-49ac-899d-0f14fc900201
-- title:
--   BV Lévy semigroup right derivative equals the full generator for C1 globally Lipschitz payoffs
-- statement:
--   For a spectrally negative Levy process with standing finite-mean assumptions and bounded-variation paths, take any globally C1 Lipschitz test payoff with integrable Levy-generator jump term. The right time derivative at zero of its transition expected payoff, started at any deterministic reserve x, equals the canonical Levy generator at x. The global Lipschitz hypothesis supplies controlled growth, while bounded variation permits the C1 generator. This is the missing analytic bridge between the Proved generator/HJB inequalities and the Proved discounted-semigroup and adapted one-step stochastic dividend budgets. It is a general-payoff extension of the already Proved exponential-test-function generator limit.
-- source:
--   Avram, Palmowski and Pistorius (2007), proof of Proposition 4(i), Section 5.4; general Lévy transition semigroup generator relationship and bounded-variation Ito change-of-variable.

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.bv_levy_transition_right_generator_of_global_C1_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (hgen : X.GeneratorIntegrable w x) :
    Tendsto
      (fun h : ℝ =>
        h⁻¹ * ((∫ ω, w (x + X.X (Real.toNNReal h) ω) ∂P) - w x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (X.generator w x)) := by sorry
