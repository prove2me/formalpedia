-- Prove2me | Theorems.Thm_Erdos970_Complex_Hadamard_hadamardQuotient_norm_le_exp_on_cartan_circle_jb247
-- name    : Erdos970.Complex.Hadamard.hadamardQuotient_norm_le_exp_on_cartan_circle_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:45:49.467683+00:00
-- url     : https://prove2.me/theorems/b2b3642c-df8c-40a2-ae49-b837d907d8ef
-- title:
--   Erdos970.Complex.Hadamard.hadamardQuotient_norm_le_exp_on_cartan_circle_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `Erdos970.Complex.Hadamard`, with `open Set Filter _root_.Asymptotics`, `open scoped Topology BigOperators`, `open _root_.Complex`):
--
--   ```lean
--   theorem hadamardQuotient_norm_le_exp_on_cartan_circle_jb247
--       {f H : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ} {Cf : ℝ}
--       (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
--       (hτ_nonneg : 0 ≤ τ) (hentire : Differentiable ℂ f)
--       (hnot : ∃ z : ℂ, f z ≠ 0)
--       (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
--         ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
--       (hsumτ : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
--         ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ))
--       (hf_boundτ : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (Cf * (1 + ‖z‖) ^ τ))
--       (hfactor : ∀ z : ℂ,
--         f z =
--           H z * z ^ analyticOrderNatAt f 0 *
--             divisorCanonicalProduct m f (Set.univ : Set ℂ) z) :
--       let Sτ : ℝ :=
--         ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
--       let Cprod : ℝ := cartanProductConstant m τ Sτ
--       ∀ {R r : ℝ}, 0 < R → 1 ≤ R → R ≤ r → r ≤ 2 * R → 0 < r →
--         ∀ (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
--           (hsmall_fin : smallSet.Finite),
--           smallSet =
--               {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
--                 ‖divisorZeroIndex₀_val p‖ ≤ 4 * R} →
--           (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
--            let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
--             fun p => ‖divisorZeroIndex₀_val p‖
--            r ∉ small.image a) →
--           (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
--            let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
--             fun p => ‖divisorZeroIndex₀_val p‖
--            (∑ p ∈ small, (1 : ℝ) * CartanBound.φ (r / a p)) ≤
--             CartanBound.Cφ * (small.card : ℝ)) →
--           ∀ u : ℂ, ‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ)
--   ```
--
--   **Definitions.** The statement is written with `Complex.CartanBound.Cφ`, `Complex.CartanBound.φ`, `Erdos970.Complex.Hadamard.cartanProductConstant`, `Erdos970.Complex.Hadamard.divisorCanonicalProduct`, `Erdos970.Complex.Hadamard.divisorZeroIndex₀` and `Erdos970.Complex.Hadamard.divisorZeroIndex₀_val` (definitions bundle `OAIQ247J000` of this split).
--
--   **Used by.** The proof of `Erdos970.Complex.Hadamard.hadamardQuotient_norm_le_exp_rpow_of_growth_jb247` of this split imports it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

open Set Filter _root_.Asymptotics
open scoped Topology BigOperators

namespace Erdos970
namespace Complex.Hadamard
open _root_.Complex

theorem hadamardQuotient_norm_le_exp_on_cartan_circle_jb247
    {f H : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ} {Cf : ℝ}
    (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hτ_nonneg : 0 ≤ τ) (hentire : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (hsumτ : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ))
    (hf_boundτ : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (Cf * (1 + ‖z‖) ^ τ))
    (hfactor : ∀ z : ℂ,
      f z =
        H z * z ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) z) :
    let Sτ : ℝ :=
      ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
    let Cprod : ℝ := cartanProductConstant m τ Sτ
    ∀ {R r : ℝ}, 0 < R → 1 ≤ R → R ≤ r → r ≤ 2 * R → 0 < r →
      ∀ (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
        (hsmall_fin : smallSet.Finite),
        smallSet =
            {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
              ‖divisorZeroIndex₀_val p‖ ≤ 4 * R} →
        (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖divisorZeroIndex₀_val p‖
         r ∉ small.image a) →
        (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖divisorZeroIndex₀_val p‖
         (∑ p ∈ small, (1 : ℝ) * CartanBound.φ (r / a p)) ≤
          CartanBound.Cφ * (small.card : ℝ)) →
        ∀ u : ℂ, ‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
  sorry

end Complex.Hadamard
end Erdos970
end
end
