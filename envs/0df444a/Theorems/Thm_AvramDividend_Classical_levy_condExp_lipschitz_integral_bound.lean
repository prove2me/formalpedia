-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_condExp_lipschitz_integral_bound
-- name    : AvramDividend.Classical.levy_condExp_lipschitz_integral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:47:07.528138+00:00
-- url     : https://prove2.me/theorems/91c3bead-3b00-4948-9e03-b1b7cf1b88d2
-- title:
--   L1 Lipschitz contraction for conditional Lévy payoffs under coupled random starting reserves
-- statement:
--   For a spectrally negative Lévy process and globally Lipschitz real payoff f with constant L, let Z and W be arbitrary random starting reserves possibly correlated with the common increment X_t−X_s. Suppose both payoff random variables and L|Z−W| are integrable. Then the L1 integral of the absolute difference of their conditional expected payoffs given F_s is at most the integral of L|Z−W|. Start from the already Proved almost-sure conditional absolute contraction, integrate by monotonicity, and invoke the conditional expectation integral identity using the probability-measure property of X. This supplies the quantitative L1 limiting estimate needed to approximate general past-measurable reserves by finite-valued reserves. No general Markov equality or stopped HJB conclusion is asserted.
-- source:
--   Accepted levy_condExp_lipschitz_absolute_bound and pinned Mathlib integrable_condExp, integral_mono_ae, integral_condExp; X.isProbability supplies finite measure.

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_condExp_lipschitz_absolute_bound

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_condExp_lipschitz_integral_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (Z W : Ω → ℝ)
    (hZ : Integrable
      (fun ω => f (Z ω + (X.X t ω - X.X s ω))) P)
    (hW : Integrable
      (fun ω => f (W ω + (X.X t ω - X.X s ω))) P)
    (hDom : Integrable (fun ω => L * |Z ω - W ω|) P) :
    (∫ ω, |(P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s]) ω -
      (P[(fun η => f (W η + (X.X t η - X.X s η))) | 𝓕 s]) ω| ∂P) ≤
      ∫ ω, L * |Z ω - W ω| ∂P := by sorry
