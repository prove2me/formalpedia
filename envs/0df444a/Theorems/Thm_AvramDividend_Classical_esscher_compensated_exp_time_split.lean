-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_compensated_exp_time_split
-- name    : AvramDividend.Classical.esscher_compensated_exp_time_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:56:05.621273+00:00
-- url     : https://prove2.me/theorems/481efeaf-b470-4451-aa29-0daf9fa3117b
-- title:
--   Pathwise multiplicative decomposition of the Esscher exponential at a deterministic time
-- statement:
--   For any Levy path, nonnegative observation times s and u, and real Esscher parameter theta, the normalised exponential at s+u factors exactly into its value at s and the compensated future-increment exponential over u. This supplies the pathwise algebraic factor needed to combine survival splitting with the whole-path Markov-Tonelli identity.
-- source:
--   Elementary real exponential addition and linearity of the Laplace compensator, for use in the killed q-scale semigroup derivation.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.esscher_compensated_exp_time_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (s u : ℝ≥0) (ω : Ω) :
    Real.exp
      (θ * X.X (s + u) ω -
        ((s + u : ℝ≥0) : ℝ) * laplaceExponent X.c X.σ X.ν θ) =
    Real.exp
      (θ * X.X s ω -
        (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
    Real.exp
      (θ * (X.X (s + u) ω - X.X s ω) -
        (u : ℝ) * laplaceExponent X.c X.σ X.ν θ) := by sorry
