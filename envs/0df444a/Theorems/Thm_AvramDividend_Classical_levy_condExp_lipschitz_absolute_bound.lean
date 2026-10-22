-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_condExp_lipschitz_absolute_bound
-- name    : AvramDividend.Classical.levy_condExp_lipschitz_absolute_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:16:45.167324+00:00
-- url     : https://prove2.me/theorems/b9a694d0-4c86-4aca-b347-938a1dbd57eb
-- title:
--   Conditional L1 contraction bound for Lipschitz Lévy payoffs with coupled starting reserves
-- statement:
--   For arbitrary random starting reserves Z and W, globally Lipschitz payoff f and the common Lévy increment X_t-X_s, the almost-sure absolute difference of the two conditional expected payoffs given the past filtration is bounded by the conditional expected Lipschitz envelope L|Z-W|. Assume integrability of the two shifted payoffs and the envelope. This exact pointwise-a.e. conditional contraction follows from the already Proved two-sided conditional comparison theorem and the pinned linearity of conditional expectation, condExp_add. It is an essential quantitative ingredient for extending the finite-valued conditional Markov identity to a general integrable F_s-measurable starting reserve via simple-function approximation. It does not claim the approximation theorem or the general stopped HJB budget itself.
-- source:
--   Proved levy_condExp_lipschitz_reserve_comparison target 1925e057-77da-4bc1-aa72-2c626dbee1e6 and pinned MeasureTheory.condExp_add.

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_condExp_lipschitz_reserve_comparison

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_condExp_lipschitz_absolute_bound
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
    ∀ᵐ ω ∂P,
      |(P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s]) ω -
        (P[(fun η => f (W η + (X.X t η - X.X s η))) | 𝓕 s]) ω| ≤
      (P[(fun η => L * |Z η - W η|) | 𝓕 s]) ω := by sorry
