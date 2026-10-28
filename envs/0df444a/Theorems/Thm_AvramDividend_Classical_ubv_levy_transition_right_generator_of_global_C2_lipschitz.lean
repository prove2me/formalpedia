-- Prove2me | Theorems.Thm_AvramDividend_Classical_ubv_levy_transition_right_generator_of_global_C2_lipschitz
-- name    : AvramDividend.Classical.ubv_levy_transition_right_generator_of_global_C2_lipschitz
-- status  : Open
-- author  : @WillR
-- created : 2026-10-25T22:36:26.602175+00:00
-- url     : https://prove2.me/theorems/236ff61f-7bbe-42c7-a6d3-5936810eac48
-- title:
--   Unbounded-variation Lévy semigroup right derivative equals its generator for C2 Lipschitz payoffs
-- statement:
--   For a spectrally negative Levy process satisfying the standing finite-mean assumptions and having unbounded-variation paths, the right derivative at zero of the transition expectation of a globally C2, globally Lipschitz payoff equals the canonical Levy generator wherever its jump term is integrable. The C2 hypothesis supports the Gaussian and compensated-small-jump Taylor terms, and the Lipschitz estimate controls large-jump growth. This supplies the unbounded-variation analogue of the general-payoff semigroup/generator bridge missing from the stochastic verification of Proposition 4(i).
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 5.4 and Proposition 4(i); standard Lévy Itô formula and generator-to-semigroup derivative correspondence for C2 test functions.

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.ubv_levy_transition_right_generator_of_global_C2_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hUBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (hwC2 : ContDiff ℝ 2 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (hgen : X.GeneratorIntegrable w x) :
    Tendsto
      (fun h : ℝ =>
        h⁻¹ * ((∫ ω, w (x + X.X (Real.toNNReal h) ω) ∂P) - w x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (X.generator w x)) := by sorry
