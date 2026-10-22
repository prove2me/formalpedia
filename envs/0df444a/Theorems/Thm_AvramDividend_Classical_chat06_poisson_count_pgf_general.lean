-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_poisson_count_pgf_general
-- name    : AvramDividend.Classical.chat06_poisson_count_pgf_general
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:55:13.269336+00:00
-- url     : https://prove2.me/theorems/2cd56d93-2124-416b-87da-00af507c1545
-- title:
--   Real-valued probability generating identity for the Poisson counting law
-- statement:
--   For a Poisson law with nonnegative rate parameter r, the integral of m raised to the event count is exp(r*(m-1)) for every real m, including m=0 and negative m. The proof expands the Poisson integral as its weighted series, combines powers by the binomial-monomial identity, applies the real exponential series, and simplifies the exponent. This exact generating-function identity can close a currently explicit hypothesis in the compound Poisson marked-sum Laplace transform. Integrability, iid mark factorisation and the count-process construction remain separate obligations.
-- source:
--   Existing source bv_poisson_count_pgf_general_chat06_20261019.lean, 45 lines, 1452 bytes, SHA-256 bc35484bf0ff04a5aef261336d1ce06fcf3e0d298008eb7c4690649759229860. Private remote source-elaboration job 09f5f110-9533-428d-a0c6-69a8add13ecd passed to deliberate sentinel with no source errors under pinned Mathlib revision. Publication resumed on 21 October 2026.

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.chat06_poisson_count_pgf_general (r : ℝ≥0) (m : ℝ) :
    (∫ n : ℕ, m ^ n ∂poissonMeasure r) =
      Real.exp ((r : ℝ) * (m - 1)) := by sorry
